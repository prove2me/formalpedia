-- Prove2me | solution 1 for AvramDividend.Classical.avram_p2_m_uniqueness_exp_image_negative_support_Ioo
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-04T09:22:53.06677+00:00
-- url     : https://prove2.me/submissions/d5bbee3d-4d5b-4c0b-aedb-aee517e7f3ef

import Mathlib

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped ENNReal

/-- A density does not introduce mass outside its source support.
The exponential image of a strictly negative source is contained in `(0,1)`. -/
theorem solution (σ : Measure ℝ) (w : ℝ → ℝ≥0∞)
    (hneg : ∀ᵐ y ∂σ, y < 0) :
    ∀ᵐ z ∂((σ.withDensity w).map Real.exp), z ∈ Ioo (0 : ℝ) 1 := by
  apply (ae_map_iff Real.measurable_exp.aemeasurable measurableSet_Ioo).mpr
  have hneg' : ∀ᵐ y ∂σ.withDensity w, y < 0 :=
    (withDensity_absolutelyContinuous σ w).ae_le hneg
  filter_upwards [hneg'] with y hy
  change 0 < Real.exp y ∧ Real.exp y < 1
  constructor
  · exact Real.exp_pos y
  · simpa only [Real.exp_zero] using (Real.exp_lt_exp.mpr hy)
