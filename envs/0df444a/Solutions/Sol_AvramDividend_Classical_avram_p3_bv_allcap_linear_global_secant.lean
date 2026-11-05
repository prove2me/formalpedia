-- Prove2me | solution 1 for AvramDividend.Classical.avram_p3_bv_allcap_linear_global_secant
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-04T14:19:43.853275+00:00
-- url     : https://prove2.me/submissions/806874b9-05df-4a8b-ae48-5d253ebf5e72

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave3_03_bv_full_cap_gradient_secant
import Theorems.Thm_AvramDividend_Classical_avram_p3_bv_finite_cap_linear_global_secant

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/- The canonical cap-linear continuation has all dividend secants
for both finite and infinite caps, with only BV interior C1 data. -/
theorem solution
    (C : ℝ≥0∞) (hC : 0 < C)
    (w : ℝ → ℝ)
    (hw_cont : ContinuousOn w (Ici 0))
    (hw_smooth : ContDiffOn ℝ 1 w
      {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (hw_grad : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C → 1 ≤ deriv w y) :
    let V : ℝ → ℝ := fun z =>
      if C = ⊤ then w z
      else if z ≤ C.toReal then w z
      else w C.toReal + (z - C.toReal)
    ∀ (a b : ℝ), 0 ≤ a → a ≤ b → b - a ≤ V b - V a := by
  let V : ℝ → ℝ := fun z =>
    if C = ⊤ then w z
    else if z ≤ C.toReal then w z
    else w C.toReal + (z - C.toReal)
  change ∀ (a b : ℝ), 0 ≤ a → a ≤ b → b - a ≤ V b - V a
  intro a b ha hab
  by_cases htop : C = ⊤
  · have hsec := avram_wave3_03_bv_full_cap_gradient_secant
      C hC w hw_cont hw_smooth hw_grad a b ha hab (by rw [htop]; exact le_top)
    dsimp only [V]
    simp only [if_pos htop]
    exact hsec
  · have hfin := avram_p3_bv_finite_cap_linear_global_secant
      C hC htop w hw_cont hw_smooth hw_grad
    change ∀ (a b : ℝ), 0 ≤ a → a ≤ b →
      b - a ≤
        (if b ≤ C.toReal then w b else w C.toReal + (b - C.toReal)) -
        (if a ≤ C.toReal then w a else w C.toReal + (a - C.toReal)) at hfin
    dsimp only [V]
    simp only [if_neg htop]
    exact hfin a b ha hab
