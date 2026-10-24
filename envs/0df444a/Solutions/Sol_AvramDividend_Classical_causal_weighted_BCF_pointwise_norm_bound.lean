-- Prove2me | solution 1 for AvramDividend.Classical.causal_weighted_BCF_pointwise_norm_bound
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-23T07:12:47.689058+00:00
-- url     : https://prove2.me/submissions/43fb8686-5b6d-4320-9218-3f83dd638dd9

import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Topology.ContinuousMap.Bounded.Normed
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical
open scoped NNReal ENNReal

/-- The exponential weight cancels and leaves the BCF supremum norm. -/
theorem solution
    (f : BoundedContinuousFunction ℝ≥0 ℝ) (w x : ℝ) :
    Real.exp (-(w * x)) *
      |Real.exp (w * x) * f ⟨max x 0, le_max_right x 0⟩| ≤ ‖f‖ := by
  have hcancel : Real.exp (-(w * x)) * Real.exp (w * x) = 1 := by
    rw [← Real.exp_add]
    simp
  calc
    Real.exp (-(w * x)) *
        |Real.exp (w * x) * f ⟨max x 0, le_max_right x 0⟩| =
        (Real.exp (-(w * x)) * Real.exp (w * x)) *
          |f ⟨max x 0, le_max_right x 0⟩| := by
            rw [abs_mul, abs_of_pos (Real.exp_pos _)]
            ring
    _ = |f ⟨max x 0, le_max_right x 0⟩| := by rw [hcancel]; ring
    _ ≤ ‖f‖ := by
      simpa only [Real.norm_eq_abs] using
        f.norm_coe_le_norm ⟨max x 0, le_max_right x 0⟩
