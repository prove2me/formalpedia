-- Prove2me | solution 1 for AvramDividend.Classical.avram_p3_bv_allcap_linear_monotone_nonnegative
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-04T14:40:14.208813+00:00
-- url     : https://prove2.me/submissions/5142c7b2-fd22-4b52-b13c-17ac79d2910a

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p3_bv_allcap_linear_global_secant

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/- Canonical BV HJB gradient forces the cap-linear extension to be
monotone on every nonnegative reserve, including all boundary contacts. -/
theorem solution
    (C : ℝ≥0∞) (hC : 0 < C)
    (w : ℝ → ℝ)
    (hw_cont : ContinuousOn w (Ici 0))
    (hw_smooth : ContDiffOn ℝ 1 w
      {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (hw_grad : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C → 1 ≤ deriv w y) :
    MonotoneOn (fun z : ℝ =>
      if C = ⊤ then w z
      else if z ≤ C.toReal then w z
      else w C.toReal + (z - C.toReal)) (Ici 0) := by
  let V : ℝ → ℝ := fun z =>
    if C = ⊤ then w z
    else if z ≤ C.toReal then w z
    else w C.toReal + (z - C.toReal)
  have hsec := avram_p3_bv_allcap_linear_global_secant
    C hC w hw_cont hw_smooth hw_grad
  change ∀ (a b : ℝ), 0 ≤ a → a ≤ b → b - a ≤ V b - V a at hsec
  change MonotoneOn V (Ici 0)
  intro a ha b hb hab
  have h := hsec a b (mem_Ici.mp ha) hab
  linarith
