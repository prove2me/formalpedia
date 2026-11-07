-- Prove2me | solution 1 for AvramDividend.Classical.avram_p3_grid4_finite_cap_C1_uniform_cutoff_defect_bound
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-06T09:36:19.840329+00:00
-- url     : https://prove2.me/submissions/fa842040-4520-4712-87ac-09681fd83223

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave3_03_bv_full_cap_gradient_secant
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- Uniform C¹ cap-corner source-error bound with no boundary derivative:
the cutoff defect controls every nonnegative reserve, including beyond cap. -/
theorem solution
    (C : ℝ≥0∞) (hC : 0 < C) (hfinite : C ≠ ⊤)
    (w : ℝ → ℝ)
    (hw_cont : ContinuousOn w (Ici 0))
    (hw_smooth : ContDiffOn ℝ 1 w
      {z : ℝ | 0 < z ∧ ENNReal.ofReal z < C})
    (hw_grad : ∀ z : ℝ, 0 < z →
      ENNReal.ofReal z < C → 1 ≤ deriv w z)
    (b y : ℝ) (hb0 : 0 ≤ b) (hbC : b ≤ C.toReal)
    (hy : 0 ≤ y) :
    0 ≤ (if y ≤ C.toReal then w y
         else w C.toReal + (y - C.toReal)) -
        (if y ≤ b then w y else w b + (y - b)) ∧
    (if y ≤ C.toReal then w y
     else w C.toReal + (y - C.toReal)) -
      (if y ≤ b then w y else w b + (y - b)) ≤
        (w C.toReal - w b) - (C.toReal - b) := by
  have hcReal : ENNReal.ofReal C.toReal ≤ C :=
    le_of_eq (ENNReal.ofReal_toReal hfinite)
  have hbc :=
    avram_wave3_03_bv_full_cap_gradient_secant
      C hC w hw_cont hw_smooth hw_grad
      b C.toReal hb0 hbC hcReal
  have hDef : 0 ≤ (w C.toReal - w b) - (C.toReal - b) := by
    linarith
  by_cases hyc : y ≤ C.toReal
  · by_cases hyb : y ≤ b
    · simp only [if_pos hyc, if_pos hyb, sub_self]
      exact ⟨le_refl _, hDef⟩
    · have hby : b ≤ y := le_of_not_ge hyb
      have hyCap : ENNReal.ofReal y ≤ C :=
        (ENNReal.ofReal_le_ofReal hyc).trans hcReal
      have hbySec :=
        avram_wave3_03_bv_full_cap_gradient_secant
          C hC w hw_cont hw_smooth hw_grad
          b y hb0 hby hyCap
      have hycSec :=
        avram_wave3_03_bv_full_cap_gradient_secant
          C hC w hw_cont hw_smooth hw_grad
          y C.toReal hy hyc hcReal
      simp only [if_pos hyc, if_neg hyb]
      constructor <;> linarith
  · have hyb : ¬ y ≤ b := by
      intro h
      exact hyc (le_trans h hbC)
    simp only [if_neg hyc, if_neg hyb]
    constructor <;> linarith
