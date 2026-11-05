-- Prove2me | solution 1 for AvramDividend.Classical.avram_p2_m_uniqueness_negative_exp_fourth_weighted_image_unit_support
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-04T07:17:35.947908+00:00
-- url     : https://prove2.me/submissions/96bf574b-74d8-49cd-9901-2289555e0e0b

import Mathlib

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter Topology
open scoped ENNReal

/-- Strictly negative marks give a fourth-weighted exponential image
supported on the compact interval [0, 1]. No finiteness is needed. -/
theorem solution
    (σ : Measure ℝ) (hnegσ : ∀ᵐ y ∂σ, y < 0) :
    ∀ᵐ z ∂((σ.withDensity
      (fun y => ENNReal.ofReal ((Real.exp y - 1) ^ 4))).map Real.exp),
      z ∈ Icc (0 : ℝ) 1 := by
  let w : ℝ → ℝ≥0∞ := fun y => ENNReal.ofReal ((Real.exp y - 1) ^ 4)
  have hw : Measurable w := by
    dsimp [w]
    fun_prop
  have hnegw : ∀ᵐ y ∂σ.withDensity w, y < 0 := by
    rw [ae_withDensity_iff hw]
    filter_upwards [hnegσ] with y hy hn
    exact hy
  change ∀ᵐ z ∂(σ.withDensity w).map Real.exp, z ∈ Icc (0 : ℝ) 1
  apply (ae_map_iff Real.measurable_exp.aemeasurable measurableSet_Icc).mpr
  filter_upwards [hnegw] with y hy
  exact ⟨(Real.exp_pos y).le, (Real.exp_lt_one_iff.mpr hy).le⟩
