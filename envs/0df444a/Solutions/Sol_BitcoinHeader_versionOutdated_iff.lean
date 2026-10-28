-- Prove2me | solution 1 for BitcoinHeader.versionOutdated_iff
-- status  : ACCEPTED   (prove)
-- author  : @pitimespi
-- created : 2026-10-26T04:37:13.789491+00:00
-- url     : https://prove2.me/submissions/c8782649-c4e9-4049-b96a-bd2a41ea6a1c

import Definitions.Def_BitcoinHeader

open BitcoinHeader

theorem solution (version : Int) (prevHeight : Nat) :
    BitcoinHeader.versionOutdated version prevHeight = true ↔
      (version < 2 ∧ BitcoinHeader.BIP34Height ≤ prevHeight + 1) ∨
      (version < 3 ∧ BitcoinHeader.BIP66Height ≤ prevHeight + 1) ∨
      (version < 4 ∧ BitcoinHeader.BIP65Height ≤ prevHeight + 1) := by
  unfold versionOutdated activeAfter
  simp only [Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq]
  constructor
  · rintro ((h | h) | h)
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr h)
  · rintro (h | h | h)
    · exact Or.inl (Or.inl h)
    · exact Or.inl (Or.inr h)
    · exact Or.inr h
