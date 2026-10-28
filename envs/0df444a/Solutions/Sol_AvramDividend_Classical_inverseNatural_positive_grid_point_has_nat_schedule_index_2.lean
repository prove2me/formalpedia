-- Prove2me | solution 2 for AvramDividend.Classical.inverseNatural_positive_grid_point_has_nat_schedule_index
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-25T19:45:13.015008+00:00
-- url     : https://prove2.me/submissions/af9bd51b-3cbd-495e-8a7c-2e8487866288

import Mathlib.Data.Nat.Pairing
import Mathlib.Data.NNReal.Defs

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open scoped NNReal

/-! Enumerate positive inverse-natural mesh points by one natural index. -/
theorem solution
    (n k : ℕ) (hn : 0 < n) :
    ∃ j : ℕ,
      ((Nat.unpair j).2 : ℝ≥0) *
        (((((Nat.unpair j).1 + 1) : ℕ) : ℝ≥0)⁻¹) =
      (k : ℝ≥0) * (n : ℝ≥0)⁻¹ := by
  refine ⟨Nat.pair (n - 1) k, ?_⟩
  have hden : n - 1 + 1 = n :=
    Nat.sub_add_cancel (Nat.succ_le_of_lt hn)
  simp [Nat.unpair_pair, hden]
