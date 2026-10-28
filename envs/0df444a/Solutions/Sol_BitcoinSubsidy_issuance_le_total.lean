-- Prove2me | solution 1 for BitcoinSubsidy.issuance_le_total
-- status  : ACCEPTED   (prove)
-- author  : @pitimespi
-- created : 2026-10-26T04:36:51.775971+00:00
-- url     : https://prove2.me/submissions/743e1033-b89b-4756-a23f-aff3d44e42bb

import Definitions.Def_BitcoinSubsidy
import Theorems.Thm_BitcoinSubsidy_issuance_total
import Theorems.Thm_BitcoinSubsidy_subsidy_zero_iff

open BitcoinSubsidy

private theorem issued_mono (a b : Nat) (h : a ≤ b) : issuedBelow a ≤ issuedBelow b := by
  induction b with
  | zero => cases Nat.le_zero.1 h; exact Nat.le_refl _
  | succ b ih =>
    rcases Nat.le_succ_iff.1 h with h' | h'
    · exact Nat.le_trans (ih h') (Nat.le_add_right _ _)
    · subst h'; exact Nat.le_refl _

private theorem issued_stable (n : Nat) (h : zeroHeight ≤ n) : issuedBelow n = issuedBelow zeroHeight := by
  induction n with
  | zero => cases Nat.le_zero.1 h
  | succ n ih =>
    rcases Nat.le_succ_iff.1 h with h' | h'
    · rw [issuedBelow, ih h', (BitcoinSubsidy.subsidy_zero_iff n).2 h', Nat.add_zero]
    · rw [h']

theorem solution (n : Nat) : issuedBelow n ≤ 2099999997690000 := by
  rw [← BitcoinSubsidy.issuance_total]
  by_cases h : zeroHeight ≤ n
  · rw [issued_stable n h]; exact Nat.le_refl _
  · exact issued_mono n zeroHeight (Nat.le_of_not_le h)
