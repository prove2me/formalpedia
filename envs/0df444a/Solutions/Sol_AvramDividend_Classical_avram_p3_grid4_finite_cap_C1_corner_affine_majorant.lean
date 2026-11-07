-- Prove2me | solution 1 for AvramDividend.Classical.avram_p3_grid4_finite_cap_C1_corner_affine_majorant
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-06T09:31:40.975377+00:00
-- url     : https://prove2.me/submissions/7b397128-2947-46b7-8f87-9be3ccf815ec

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p3_bv_finite_cap_linear_crossing_secant
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- The finite cap affine continuation has a global supporting line without
assuming a boundary derivative at C; valid for canonical BV C¹ data. -/
theorem solution
    (C : ℝ≥0∞) (hC : 0 < C) (hfinite : C ≠ ⊤)
    (w : ℝ → ℝ)
    (hw_cont : ContinuousOn w (Ici 0))
    (hw_smooth : ContDiffOn ℝ 1 w
      {z : ℝ | 0 < z ∧ ENNReal.ofReal z < C})
    (hw_grad : ∀ z : ℝ, 0 < z →
      ENNReal.ofReal z < C → 1 ≤ deriv w z)
    (y : ℝ) (hy : 0 ≤ y) :
    (if y ≤ C.toReal then w y
     else w C.toReal + (y - C.toReal)) ≤
      w C.toReal + (y - C.toReal) := by
  by_cases hyC : y ≤ C.toReal
  · simp only [if_pos hyC]
    have hs :=
      avram_p3_bv_finite_cap_linear_crossing_secant
        C hC hfinite w hw_cont hw_smooth hw_grad
        y C.toReal hy hyC le_rfl
    linarith
  · simp [hyC]
