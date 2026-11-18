-- Prove2me | solution 1 for AvramDividend.Classical.avram_gaussianB_NNReal_first_contact_floor_real_physical_times
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-18T01:06:14.293652+00:00
-- url     : https://prove2.me/submissions/060857c1-d010-4eda-b170-a933a72b2c70

import Mathlib.Data.NNReal.Defs
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open scoped NNReal
noncomputable section
/-- Transfer true Gaussian first-contact strict floor to real occupation times. -/
theorem solution
    (f : ℝ≥0 → ℝ) (T : ℝ≥0) (b : ℝ)
    (hFloor : ∀ t : ℝ≥0, t < T → b < f t) :
    ∀ u : ℝ, 0 < u → u < (T : ℝ) →
      b < f (Real.toNNReal u) := by
  intro u hu hT
  have hlt : Real.toNNReal u < T :=
    (Real.toNNReal_lt_iff_lt_coe hu.le).2 hT
  exact hFloor (Real.toNNReal u) hlt
