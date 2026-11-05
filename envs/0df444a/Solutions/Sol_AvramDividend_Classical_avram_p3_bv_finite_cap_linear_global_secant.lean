-- Prove2me | solution 1 for AvramDividend.Classical.avram_p3_bv_finite_cap_linear_global_secant
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-04T14:16:53.843632+00:00
-- url     : https://prove2.me/submissions/22ddd7ab-498d-43ef-8ee6-9d73b4224c24

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave3_03_bv_full_cap_gradient_secant
import Theorems.Thm_AvramDividend_Classical_avram_p3_bv_finite_cap_linear_crossing_secant

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/- Exact all-reserve dividend secants of the canonical slope-one
finite-cap continuation; no regularity of w outside the cap. -/
theorem solution
    (C : ℝ≥0∞) (hC : 0 < C) (hfinite : C ≠ ⊤)
    (w : ℝ → ℝ)
    (hw_cont : ContinuousOn w (Ici 0))
    (hw_smooth : ContDiffOn ℝ 1 w
      {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (hw_grad : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C → 1 ≤ deriv w y) :
    let V : ℝ → ℝ := fun z =>
      if z ≤ C.toReal then w z else w C.toReal + (z - C.toReal)
    ∀ (a b : ℝ), 0 ≤ a → a ≤ b → b - a ≤ V b - V a := by
  let V : ℝ → ℝ := fun z =>
    if z ≤ C.toReal then w z else w C.toReal + (z - C.toReal)
  change ∀ (a b : ℝ), 0 ≤ a → a ≤ b → b - a ≤ V b - V a
  intro a b ha hab
  by_cases hb : b ≤ C.toReal
  · have haC : a ≤ C.toReal := le_trans hab hb
    have hbCap : ENNReal.ofReal b ≤ C := by
      calc
        ENNReal.ofReal b ≤ ENNReal.ofReal C.toReal :=
          ENNReal.ofReal_le_ofReal hb
        _ = C := ENNReal.ofReal_toReal hfinite
    have hsec := avram_wave3_03_bv_full_cap_gradient_secant
      C hC w hw_cont hw_smooth hw_grad a b ha hab hbCap
    dsimp only [V]
    rw [if_pos hb, if_pos haC]
    exact hsec
  · have hCb : C.toReal ≤ b := le_of_lt (lt_of_not_ge hb)
    by_cases haC : a ≤ C.toReal
    · have hsec := avram_p3_bv_finite_cap_linear_crossing_secant
        C hC hfinite w hw_cont hw_smooth hw_grad a b ha haC hCb
      dsimp only [V]
      rw [if_neg hb, if_pos haC]
      exact hsec
    · dsimp only [V]
      rw [if_neg hb, if_neg haC]
      linarith
