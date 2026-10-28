-- Prove2me | solution 1 for BitcoinPow.checkProofOfWork_iff
-- status  : ACCEPTED   (prove)
-- author  : @pitimespi
-- created : 2026-10-26T04:36:54.073461+00:00
-- url     : https://prove2.me/submissions/a7c321cc-0c8c-4f0d-b9d4-b39b8c0b633d

import Definitions.Def_BitcoinPow
import Theorems.Thm_BitcoinPow_setCompact_eq_spec

open BitcoinPow

theorem solution (hash : Nat) (nBits : BitVec 32) :
    BitcoinPow.checkProofOfWork hash nBits = true ↔
      BitcoinPow.compactNegative nBits = false ∧ BitcoinPow.compactOverflow nBits = false ∧
      0 < BitcoinPow.specTarget nBits ∧ BitcoinPow.specTarget nBits ≤ BitcoinPow.powLimit ∧
      hash ≤ BitcoinPow.specTarget nBits := by
  unfold checkProofOfWork deriveTarget
  simp only []
  by_cases hc : (compactNegative nBits || decide (setCompact nBits = 0) || compactOverflow nBits ||
      decide (powLimit < setCompact nBits)) = true
  · rw [if_pos hc]
    simp only [Bool.or_eq_true, decide_eq_true_eq] at hc
    simp only [Bool.false_eq_true, false_iff]
    rintro ⟨hneg, hov, hpos, hlim, -⟩
    have hs := BitcoinPow.setCompact_eq_spec nBits hov
    rw [hneg, hov, hs] at hc
    simp only [Bool.false_eq_true, false_or, or_false] at hc
    omega
  · rw [if_neg hc]
    simp only [Bool.or_eq_true, decide_eq_true_eq, not_or] at hc
    obtain ⟨⟨⟨hneg, hzero⟩, hov⟩, hlim⟩ := hc
    have hneg' : compactNegative nBits = false := by
      cases h : compactNegative nBits
      · rfl
      · exact absurd h hneg
    have hov' : compactOverflow nBits = false := by
      cases h : compactOverflow nBits
      · rfl
      · exact absurd h hov
    have hs := BitcoinPow.setCompact_eq_spec nBits hov'
    rw [hs] at hzero hlim ⊢
    simp only [decide_eq_true_eq]
    constructor
    · intro h; exact ⟨hneg', hov', by omega, by omega, h⟩
    · rintro ⟨-, -, -, -, h⟩; exact h
