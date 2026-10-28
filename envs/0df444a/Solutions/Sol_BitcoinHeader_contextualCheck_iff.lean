-- Prove2me | solution 1 for BitcoinHeader.contextualCheck_iff
-- status  : ACCEPTED   (prove)
-- author  : @pitimespi
-- created : 2026-10-26T04:37:14.356548+00:00
-- url     : https://prove2.me/submissions/8dab3a0d-61e8-462d-bfe1-d155b41c35d0

import Definitions.Def_BitcoinHeader
import Theorems.Thm_BitcoinHeader_versionOutdated_iff

open BitcoinHeader

theorem solution (h : BitcoinHeader.Header) (prevHeight : Nat) (prevTimes : List Int)
    (required : BitVec 32) (now : Int) :
    BitcoinHeader.contextualCheck h prevHeight prevTimes required now = true ↔
      h.bits = required ∧
      BitcoinHeader.medianTimePast prevTimes < h.time ∧
      h.time ≤ now + BitcoinHeader.MAX_FUTURE_BLOCK_TIME ∧
      ¬ ((h.version < 2 ∧ BitcoinHeader.BIP34Height ≤ prevHeight + 1) ∨
         (h.version < 3 ∧ BitcoinHeader.BIP66Height ≤ prevHeight + 1) ∨
         (h.version < 4 ∧ BitcoinHeader.BIP65Height ≤ prevHeight + 1)) := by
  unfold contextualCheck
  rw [← BitcoinHeader.versionOutdated_iff]
  simp only [Bool.and_eq_true, decide_eq_true_eq, Bool.not_eq_true', Bool.not_eq_true]
  constructor
  · rintro ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩
    exact ⟨h1, h2, h3, h4⟩
  · rintro ⟨h1, h2, h3, h4⟩
    exact ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩
