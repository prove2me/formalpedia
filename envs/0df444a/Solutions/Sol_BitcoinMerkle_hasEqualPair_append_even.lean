-- Prove2me | solution 1 for BitcoinMerkle.hasEqualPair_append_even
-- status  : ACCEPTED   (prove)
-- author  : @pitimespi
-- created : 2026-10-26T04:37:02.673222+00:00
-- url     : https://prove2.me/submissions/41e7e1f7-5af1-46ca-9819-f824903d71d2

import Definitions.Def_BitcoinMerkle

open BitcoinMerkle

theorem solution {H : Type} [DecidableEq H] :
    ∀ (l r : List H), l.length % 2 = 0 →
      BitcoinMerkle.hasEqualPair (l ++ r) = (BitcoinMerkle.hasEqualPair l || BitcoinMerkle.hasEqualPair r)
  | [], r, _ => by simp [hasEqualPair]
  | [a], r, h => by simp at h
  | a :: b :: rest, r, h => by
    simp only [List.length_cons] at h
    have h' : rest.length % 2 = 0 := by omega
    simp only [List.cons_append, hasEqualPair, Bool.or_assoc]
    rw [solution rest r h']
