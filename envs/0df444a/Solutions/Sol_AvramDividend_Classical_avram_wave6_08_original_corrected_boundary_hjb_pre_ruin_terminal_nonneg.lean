-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave6_08_original_corrected_boundary_hjb_pre_ruin_terminal_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-02T10:26:56.048743+00:00
-- url     : https://prove2.me/submissions/d206db32-00a7-4394-93ba-9a9dc4823085

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave3_04_allCap_admissible_initial_capital_nonneg
import Theorems.Thm_AvramDividend_Classical_capped_riskProcess_range_before_ruin_including_zero
import Theorems.Thm_AvramDividend_Classical_avram_wave3_03_bv_full_cap_gradient_secant

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

/-- Corrected nonnegative zero boundary and the HJB gradient imply that
the actual capped candidate remains nonnegative until ruin, including t = 0. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (C : ℝ≥0∞) (hC : 0 < C)
    (hxc : ENNReal.ofReal x ≤ C)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (w : ℝ → ℝ) (hw0 : 0 ≤ w 0)
    (hw_cont : ContinuousOn w (Ici 0))
    (hw_smooth : ContDiffOn ℝ 1 w
      {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (hw_grad : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C →
      1 ≤ deriv w y) :
    ∀ (ω : Ω) (t : ℝ≥0),
      (t : ℝ≥0∞) < ruinTime X x D ω →
      0 ≤ w (riskProcess X x D t ω) := by
  intro ω t ht
  have hx0 : 0 ≤ x :=
    avram_wave3_04_allCap_admissible_initial_capital_nonneg
      X x C hxc D hD
  obtain ⟨hy0, hyC⟩ :=
    capped_riskProcess_range_before_ruin_including_zero
      X x hx0 C hxc D hD ω t ht
  have hsec :
      riskProcess X x D t ω - 0 ≤
        w (riskProcess X x D t ω) - w 0 :=
    avram_wave3_03_bv_full_cap_gradient_secant
      C hC w hw_cont hw_smooth hw_grad
      0 (riskProcess X x D t ω) (le_refl 0) hy0 hyC
  linarith
