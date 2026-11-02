-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave5_ubv_original_preruin_candidate_nonnegative_from_gradient
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-01T09:44:57.858451+00:00
-- url     : https://prove2.me/submissions/64ecef02-58c0-4b5a-a533-3cbd6c8050b4

import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_riskProcess_nonneg_before_ruin
import Theorems.Thm_AvramDividend_Classical_avram_wave3_04_ubv_C2_gradient_secant_closed_all_caps

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (w : ℝ → ℝ) (C : ℝ≥0∞)
    (hw0 : 0 ≤ w 0)
    (hw_cont : ContinuousOn w (Ici 0))
    (hw_smooth : ContDiffOn ℝ 2 w
      {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (hw_grad : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C →
      1 ≤ deriv w y)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (hD : IsAdmissibleLe X x C D) :
    ∀ ω (t : ℝ≥0), 0 < t →
      (t : ℝ≥0∞) < ruinTime X x D ω →
        0 ≤ w (riskProcess X x D t ω) := by
  intro ω t ht hs
  have hy : 0 ≤ riskProcess X x D t ω :=
    riskProcess_nonneg_before_ruin X x D ω t hs
  have hcap : ENNReal.ofReal (riskProcess X x D t ω) ≤ C :=
    hD.2 ω t ht
  have hsec := avram_wave3_04_ubv_C2_gradient_secant_closed_all_caps
    C w hw_cont hw_smooth hw_grad 0 (riskProcess X x D t ω)
    (le_refl (0 : ℝ)) hy hcap
  linarith
