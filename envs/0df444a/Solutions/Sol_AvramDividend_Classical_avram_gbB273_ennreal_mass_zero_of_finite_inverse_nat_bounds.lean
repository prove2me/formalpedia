-- Prove2me | solution 1 for AvramDividend.Classical.avram_gbB273_ennreal_mass_zero_of_finite_inverse_nat_bounds
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-13T21:30:43.746203+00:00
-- url     : https://prove2.me/submissions/ca17b470-5d8d-4db3-b891-dada48778703

import Mathlib
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Filter
open scoped NNReal ENNReal
noncomputable section

/-- A bounded product-measure mass decaying at inverse mesh refinement is exactly zero. -/
theorem solution (r : ℝ≥0∞) (C : NNReal)
    (h : ∀ n : ℕ, r ≤ (C : ℝ≥0∞) * (n : ℝ≥0∞)⁻¹) :
    r = 0 := by
  have hlim : Tendsto
      (fun n : ℕ => (C : ℝ≥0∞) * (n : ℝ≥0∞)⁻¹) atTop (nhds 0) := by
    simpa only [mul_zero] using
      (ENNReal.Tendsto.const_mul ENNReal.tendsto_inv_nat_nhds_zero
        (Or.inr (by simp : (C : ℝ≥0∞) ≠ ⊤)))
  have hzero : r ≤ 0 := by
    exact ge_of_tendsto hlim (Filter.Eventually.of_forall h)
  exact le_antisymm hzero bot_le

-- Source identity rebased to the current Prove2Me submission checker after the earlier immutable snapshot changed.
