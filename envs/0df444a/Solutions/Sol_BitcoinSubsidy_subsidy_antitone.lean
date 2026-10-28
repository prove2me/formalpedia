-- Prove2me | solution 1 for BitcoinSubsidy.subsidy_antitone
-- status  : ACCEPTED   (prove)
-- author  : @pitimespi
-- created : 2026-10-26T04:36:49.494236+00:00
-- url     : https://prove2.me/submissions/fb6030aa-9bc0-4a7a-9f47-3d873504c744

import Definitions.Def_BitcoinSubsidy
import Theorems.Thm_BitcoinSubsidy_core_eq_spec

open BitcoinSubsidy

theorem solution (h₁ h₂ : Nat) (h : h₁ ≤ h₂) :
    coreSubsidy h₂ ≤ coreSubsidy h₁ := by
  rw [BitcoinSubsidy.core_eq_spec, BitcoinSubsidy.core_eq_spec]
  unfold specSubsidy
  apply Nat.div_le_div_left
  · exact Nat.pow_le_pow_right (by decide) (Nat.div_le_div_right h)
  · exact Nat.two_pow_pos _
