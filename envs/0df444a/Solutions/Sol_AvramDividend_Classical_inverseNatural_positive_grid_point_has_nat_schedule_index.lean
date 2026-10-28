-- Prove2me | solution 1 for AvramDividend.Classical.inverseNatural_positive_grid_point_has_nat_schedule_index
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-25T19:44:54.496718+00:00
-- url     : https://prove2.me/submissions/6501c65e-61c6-4fc0-9a9c-1646622bf70f

import Mathlib.Data.Nat.Pairing
import Mathlib.Data.NNReal.Defs

open scoped NNReal
theorem solution
    (n k : ℕ) (hn : 0 < n) :
    ∃ j : ℕ,
      ((Nat.unpair j).2 : ℝ≥0) *
        (((((Nat.unpair j).1 + 1) : ℕ) : ℝ≥0)⁻¹) =
      (k : ℝ≥0) * (n : ℝ≥0)⁻¹ := by
  refine ⟨Nat.pair (n - 1) k, ?_⟩
  rw [Nat.unpair_pair, Nat.sub_add_cancel hn]
