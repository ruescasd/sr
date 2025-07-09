#![allow(dead_code)]

use std::collections::BTreeSet;
use std::hash::Hash as HashTrait;

use ascent::ascent;
use stateright::{Model, Property};

#[derive(Clone, PartialEq, Eq, Hash, Debug)]
enum Action {
    ComputeShares(CfgHash),
    ComputePublicKey(CfgHash, SharesHashes),
}

#[derive(Clone, PartialEq, Eq, Hash, Debug)]
enum Message {
    ConfigurationValid(CfgHash, TrusteeCount, TrusteeIndex),
    Shares(CfgHash, TrusteeSharesHash, Sender),
    PublicKey(CfgHash, PublicKeyHash, Sender),
    // dummy value to prevent starlight from detecting a loop that thwarts eventually properties
    NOP,
}
impl Message {
    // Every message has a unique "slot". Even though checks for this should exist
    // outside our protocol logic, we can perform these checks here as well (see the duplicate error rule)
    fn collides(&self, other: &Message) -> bool {
        if let Message::NOP = self {
            return false;
        }
        if self == other {
            return false;
        }
        if std::mem::discriminant(self) != std::mem::discriminant(other) {
            return false;
        }

        match (self, other) {
            (Message::Shares(_, _shares1, sender1), Message::Shares(_, _shares2, sender2)) => {
                sender1 == sender2
            }
            _ => false,
        }
    }
}

const MAX_TRUSTEES: usize = 24;
const HASH_SIZE: usize = 3;

type TrusteeIndex = usize;
type TrusteeCount = usize;
type Hash = [u8; HASH_SIZE];

type CfgHash = Hash;
type TrusteeSharesHash = Hash;
type PublicKeyHash = Hash;
type SharesHashesAcc = AccumulatorSet<TrusteeSharesHash>;
type SharesHashes = Vec<TrusteeSharesHash>;
type PkHashesAcc = AccumulatorSet<PublicKeyHash>;
type Sender = TrusteeIndex;

mod dkg {
    use super::*;

    ascent! {
        relation error(String);
        relation message(Message);

        error(format!("duplicate message {:?}, {:?}", m1, m2)) <--
            message(m1),
            message(m2),
            if m1.collides(m2);

        relation action(Action);

        // this message comes from the setup phase
        relation configuration_valid(CfgHash, TrusteeCount, TrusteeIndex);
        configuration_valid(cfg_hash, trustee_count, self_index) <--
            message(m),
            if let Message::ConfigurationValid(cfg_hash, trustee_count, self_index) = m;

        relation shares(CfgHash, TrusteeSharesHash, Sender);
        shares(cfg_hash, shares, sender) <--
            message(m),
            if let Message::Shares(cfg_hash, shares, sender) = m,
            // extra check that cfg hash matches (even if this is checked in subsequent rules)
            configuration_valid(cfg_hash, _, _);

        action(Action::ComputeShares(*cfg_hash)) <--
            configuration_valid(cfg_hash, _, self_index),
            !shares(cfg_hash, _, self_index);

        relation public_key(CfgHash, PublicKeyHash, Sender);
        public_key(cfg_hash, pk_hash, sender) <--
            message(m),
            if let Message::PublicKey(cfg_hash, pk_hash, sender) = m,
            // extra check that cfg hash matches (even if this is checked in subsequent rules)
            configuration_valid(cfg_hash, _, _);

        relation shares_acc(CfgHash, SharesHashesAcc);
        shares_acc(cfg_hash, AccumulatorSet::new(*shares)) <-- shares(cfg_hash, shares, 1);

        shares_acc(cfg_hash, shares_hashes.add(*shares, *sender)) <--
            shares_acc(cfg_hash, shares_hashes),
            shares(cfg_hash, shares, sender);

        relation shares_all(CfgHash, SharesHashesAcc);
        shares_all(cfg_hash, shares) <--
            shares_acc(cfg_hash, shares),
            configuration_valid(cfg_hash, trustee_count, self_index),
            if shares.complete(*trustee_count);

        action(Action::ComputePublicKey(*cfg_hash, shares.extract())) <--
            configuration_valid(cfg_hash, _, self_index),
            shares_all(cfg_hash, shares),
            !public_key(cfg_hash, _, self_index);

        error(format!("pk mismatch {:?} != {:?} ({} {})", pk_hash1, pk_hash2, sender1, sender2)) <--
            public_key(cfg_hash, pk_hash1, sender1),
            public_key(cfg_hash, pk_hash2, sender2),
            if pk_hash1 != pk_hash2;

    }

    pub(crate) fn program() -> super::dkg::AscentProgram {
        AscentProgram::default()
    }
}

mod dkg_execute {
    use super::*;

    ascent! {
        relation action(Action);
        relation message(Message);
        relation active(TrusteeIndex);

        message(Message::Shares(*cfg_hash, share_stub(*trustee), *trustee)) <--
            action(compute_shares), active(trustee),
            if let Action::ComputeShares(cfg_hash) = compute_shares;

        // we use the fixed value of 1, because honest trustees will compute the same public key
        message(Message::PublicKey(*cfg_hash, pk_stub(1), *trustee)) <--
            action(compute_public_key), active(trustee),
            if let Action::ComputePublicKey(cfg_hash, shares) = compute_public_key;
    }

    pub(crate) fn program() -> super::dkg_execute::AscentProgram {
        AscentProgram::default()
    }

    pub(crate) fn share_stub(trustee: usize) -> TrusteeSharesHash {
        println!("* execute: computing shares stub with {}", trustee);
        [trustee as u8; HASH_SIZE]
    }

    pub(crate) fn pk_stub(trustee: usize) -> TrusteeSharesHash {
        println!("* execute: Computing pk stub with {}", trustee);
        [trustee as u8; HASH_SIZE]
    }
}

const DUMMY_CFG: Hash = [0u8; HASH_SIZE];

// stateright test harness
struct DkgHarness(Hash, usize);
impl Model for DkgHarness {
    type State = Vec<Message>;
    type Action = Action;

    fn init_states(&self) -> Vec<Self::State> {
        let init = vec![Message::ConfigurationValid(self.0, self.1, 1)];

        vec![init]
    }

    fn actions(&self, state: &Self::State, actions: &mut Vec<Self::Action>) {
        let mut prog = dkg::program();

        let messages: Vec<(Message,)> = state.into_iter().map(|m| (m.clone(),)).collect();
        prog.message = messages;
        prog.run();
        let mut actions_: Vec<Action> = prog.action.into_iter().map(|a| a.0).collect();

        if prog.error.len() != 0 {
            println!("* actions: found errors: {:?}", prog.error);
            return;
        }

        if actions_.len() == 0 {
            println!("** End state **");
        } else {
            println!("* actions {:?} => {:?}", state, actions_);
            actions.append(&mut actions_);
        }
    }

    fn next_state(&self, last_state: &Self::State, action: Self::Action) -> Option<Self::State> {
        let mut prog = dkg_execute::program();

        println!("* next_state action {:?}", action);
        prog.action = vec![(action.clone(),)];
        let active: Vec<(usize,)> = (1..=self.1).map(|i| (i,)).collect();
        prog.active = active;
        prog.run();
        let mut messages_: Vec<Message> = prog.message.into_iter().map(|m| m.0).collect();

        let ret = if messages_.len() > 0 {
            println!("* next_state: {:?} + {:?}", last_state, messages_);
            let mut ret = last_state.clone();
            ret.append(&mut messages_);

            Some(ret)
        } else {
            println!("* next_state: No next state *");
            None
        };
        ret

        /* else {
            println!("* next state: appending NOP");
            new_state.push(Message::NOP);
        } */

        /* let f = rand::random::<f64>();
        if f > 0.995 {
            println!("{}", f);
            new_state.append(&mut messages_);
        }
        else {
            new_state.push(Message::NOP);
        }*/
    }

    fn properties(&self) -> Vec<Property<Self>> {
        // example of how to check with fixed trustees, should dynamically derive from self.1
        vec![Property::<Self>::eventually("solved", |_, state| {
            state.contains(&Message::Shares(DUMMY_CFG, [1u8; HASH_SIZE], 1))
                && state.contains(&Message::Shares(DUMMY_CFG, [2u8; HASH_SIZE], 2))
                && state.contains(&Message::Shares(DUMMY_CFG, [3u8; HASH_SIZE], 3))
                && state.contains(&Message::PublicKey(DUMMY_CFG, [1u8; HASH_SIZE], 1))
                && state.contains(&Message::PublicKey(DUMMY_CFG, [1u8; HASH_SIZE], 2))
                && state.contains(&Message::PublicKey(DUMMY_CFG, [1u8; HASH_SIZE], 3))
        })]
    }
}

#[derive(Clone, HashTrait, PartialEq, Eq, Debug)]
struct AccumulatorSet<T> {
    values: [Option<T>; MAX_TRUSTEES],
    value_set: BTreeSet<T>,
}
impl<T: Ord + Clone> AccumulatorSet<T> {
    pub fn new(init: T) -> Self {
        AccumulatorSet {
            values: std::array::from_fn(|_| None),
            value_set: BTreeSet::new(),
        }
        .add(init, 1)
    }
    fn add(&self, rhs: T, index: TrusteeIndex) -> Self {
        let mut ret = AccumulatorSet {
            values: self.values.clone(),
            value_set: self.value_set.clone(),
        };

        if !ret.value_set.contains(&rhs) && ret.values[index] == None {
            ret.value_set.insert(rhs.clone());
            ret.values[index] = Some(rhs.clone());
        }

        ret
    }
    fn complete(&self, trustee_count: usize) -> bool {
        self.value_set.len() == trustee_count
    }

    fn extract(&self) -> Vec<T> {
        let some = self.values.iter().filter(|t| t.is_some());
        some.map(|t| t.clone().expect("impossible")).collect()
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use stateright::Checker;

    #[test]
    fn dkg() {
        let checker = DkgHarness(DUMMY_CFG, 3).checker().spawn_bfs().join();
        checker.assert_properties();
    }
}
