/*
* Design a Leaderboard Class which has the following 3 functions:
1. addScore(playerId, score): Update the leaderboard by adding score to the given player's score.
   If there is no player with such id in the leaderboard, add him to the leaderboard with the given score.
2. top(K): Return the score sum of the top K players.
3. reset(playerId): Reset the score of the player with the given id to 0 (in other words erase it from the leaderboard).
   It is guaranteed that the player was added to the leaderboard before calling this function.
*/

use std::{
    cmp::Reverse,
    collections::{BinaryHeap, HashMap},
};

/// A player ID (Pid), represented as a wrapper around a `usize` value.
/// This struct is used to uniquely identify players in the leaderboard.
#[derive(Eq, Hash, PartialEq, Copy, Clone, Debug)]
pub struct Pid(usize);

impl From<usize> for Pid {
    fn from(value: usize) -> Self {
        Self(value)
    }
}

/// A leaderboard that tracks the scores of players identified by their `Pid`.
#[derive(Debug)]
pub struct Leaderboard {
    player_scores: HashMap<Pid, u32>,
}

impl Leaderboard {
    /// Creates a new empty leaderboard.
    ///
    /// # Returns
    ///
    /// Returns a `Leaderboard` with no players and scores.
    pub fn new() -> Self {
        Self {
            player_scores: HashMap::new(),
        }
    }

    /// Retrieves the score of a player.
    ///
    /// # Arguments
    ///
    /// * `pid` - The player's ID (`Pid`) whose score is to be fetched.
    ///
    /// # Returns
    ///
    /// Returns `Some(u32)` if the player exists in the leaderboard,
    /// otherwise `None`.
    ///
    /// # Example
    ///
    /// ```
    /// use implrs::leaderboard::{Leaderboard, Pid};
    ///
    /// let mut leaderboard = Leaderboard::new();
    /// leaderboard.add_score(Pid::from(1), 100);
    /// assert_eq!(leaderboard.get(Pid::from(1)), Some(100));
    /// assert_eq!(leaderboard.get(Pid::from(2)), None);
    /// ```
    pub fn get(&self, pid: Pid) -> Option<u32> {
        self.player_scores.get(&pid).copied()
    }

    /// Adds or updates a player's score.
    ///
    /// If the player already has a score, the new score is added to the existing score.
    /// If the player does not exist, a new player with the given score is added.
    ///
    /// # Arguments
    ///
    /// * `pid` - The player's ID (`Pid`) whose score is to be updated.
    /// * `score` - The score to add to the player's current score.
    ///
    /// # Example
    ///
    /// ```
    /// use implrs::leaderboard::{Leaderboard, Pid};
    ///
    /// let mut leaderboard = Leaderboard::new();
    /// leaderboard.add_score(Pid::from(1), 50);
    /// leaderboard.add_score(Pid::from(1), 25); // Player 1's score is now 75.
    /// assert_eq!(leaderboard.get(Pid::from(1)), Some(75));
    /// ```
    pub fn add_score(&mut self, pid: Pid, score: u32) {
        self.player_scores
            .entry(pid)
            .and_modify(|prev_score| *prev_score += score)
            .or_insert(score);
    }

    /// Returns the sum of the top `k` highest scores in the leaderboard.
    ///
    /// If `k` is greater than or equal to the number of players in the leaderboard,
    /// it will return the sum of all players' scores.
    ///
    /// # Arguments
    ///
    /// * `k` - The number of top scores to sum.
    ///
    /// # Returns
    ///
    /// Returns the sum of the top `k` player scores.
    ///
    /// # Example
    ///
    /// ```
    /// use implrs::leaderboard::{Leaderboard, Pid};
    ///
    /// let mut leaderboard = Leaderboard::new();
    /// leaderboard.add_score(Pid::from(1), 10);
    /// leaderboard.add_score(Pid::from(2), 20);
    /// leaderboard.add_score(Pid::from(3), 30);
    /// assert_eq!(leaderboard.top_k(2), 50); // The sum of the top 2 scores is 50
    /// ```
    ///
    /// # Notes
    ///
    /// - If `k` is larger than the number of players in the leaderboard, the sum
    ///   of all scores will be returned.
    pub fn top_k(&self, k: usize) -> u32 {
        if k >= self.player_scores.len() {
            return self.player_scores.values().sum();
        }

        let mut heap: BinaryHeap<Reverse<u32>> = BinaryHeap::new();
        for score in self.player_scores.values() {
            heap.push(Reverse(*score));

            if heap.len() > k {
                heap.pop();
            }
        }

        heap.iter().map(|r| r.0).sum()
    }

    /// Resets the score of a player to zero.
    ///
    /// # Arguments
    ///
    /// * `pid` - The player's ID (`Pid`) whose score is to be reset.
    ///
    /// # Returns
    ///
    /// - Returns `Ok(())` if the player's score was successfully reset to zero.
    /// - Returns `Err(pid)` if the player does not exist in the leaderboard.
    ///
    /// # Example
    ///
    /// ```
    /// use implrs::leaderboard::{Leaderboard, Pid};
    ///
    /// let mut leaderboard = Leaderboard::new();
    /// leaderboard.add_score(Pid::from(1), 50);
    /// leaderboard.reset_player_score(Pid::from(1)).unwrap();
    /// assert_eq!(leaderboard.get(Pid::from(1)), Some(0));
    /// ```
    pub fn reset_player_score(&mut self, pid: Pid) -> Result<(), Pid> {
        match self.player_scores.get_mut(&pid) {
            Some(score) => {
                *score = 0;
                Ok(())
            }
            None => Err(pid),
        }
    }
}

impl Default for Leaderboard {
    fn default() -> Self {
        Self::new()
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn leaderboard_get() {
        let mut leaderboard = Leaderboard::new();
        leaderboard.add_score(Pid::from(0), 100);
        assert_eq!(leaderboard.get(Pid::from(0)), Some(100));
        assert_eq!(leaderboard.get(Pid::from(1)), None);
    }

    #[test]
    fn leaderboard_add_score() {
        let mut leaderboard = Leaderboard::new();
        let pid_1 = Pid::from(1);
        let pid_2 = Pid::from(2);
        leaderboard.add_score(pid_1, 14);
        leaderboard.add_score(pid_1, 4);
        leaderboard.add_score(pid_2, 2);

        assert_eq!(leaderboard.get(pid_1), Some(18));
        assert_eq!(leaderboard.get(pid_2), Some(2));
    }

    #[test]
    fn leaderboard_top_k() {
        let mut leaderboard = Leaderboard::new();
        leaderboard.add_score(Pid::from(0), 20);
        leaderboard.add_score(Pid::from(1), 80);
        leaderboard.add_score(Pid::from(2), 30);

        assert_eq!(leaderboard.top_k(1), 80);
        assert_eq!(leaderboard.top_k(2), 110);
        assert_eq!(leaderboard.top_k(3), 130);
        assert_eq!(leaderboard.top_k(7), 130);
    }
}
