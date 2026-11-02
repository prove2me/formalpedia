-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave5_ubv_original_finite_stopping_candidate_strict_positive_before_ruin
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-01T13:36:31.296968+00:00
-- url     : https://prove2.me/submissions/8105982a-4342-42d4-a5ee-703b33b835f5

import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave4_04_ubv_controlled_rightcont_finite_stopping_strict_positive
import Theorems.Thm_AvramDividend_Classical_admissibleLe_riskProcess_le_cap_all_times
import Theorems.Thm_AvramDividend_Classical_avram_wave3_04_ubv_C2_gradient_secant_closed_all_caps

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hBV : ¬ X.BoundedVariation)
    (w : ℝ → ℝ) (C : ℝ≥0∞)
    (hw0 : 0 ≤ w 0)
    (hw_cont : ContinuousOn w (Ici 0))
    (hw_smooth : ContDiffOn ℝ 2 w {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (hw_grad : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C → 1 ≤ deriv w y)
    (x : ℝ) (hxc : ENNReal.ofReal x ≤ C)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (τ : Ω → ℝ≥0)
    (hτ : ∀ s : ℝ≥0,
      MeasurableSet[𝓕.rightCont s] {ω : Ω | τ ω ≤ s})
    (hstop : IsStoppingTime 𝓕.rightCont
      (fun ω => (τ ω : WithTop ℝ≥0))) :
    ∀ᵐ ω ∂P, ((τ ω : ℝ≥0) : ℝ≥0∞) < ruinTime X x D ω →
      0 < w (riskProcess X x D (τ ω) ω) := by
  have hres :=
    avram_wave4_04_ubv_controlled_rightcont_finite_stopping_strict_positive
      X hBV x D hD.1.1 τ hτ hstop
  filter_upwards [hres] with ω hω
  intro hpre
  have hy : 0 < riskProcess X x D (τ ω) ω := hω hpre
  have hcap : ENNReal.ofReal (riskProcess X x D (τ ω) ω) ≤ C :=
    admissibleLe_riskProcess_le_cap_all_times X x C D hD hxc ω (τ ω)
  have hsec := avram_wave3_04_ubv_C2_gradient_secant_closed_all_caps
    C w hw_cont hw_smooth hw_grad 0 (riskProcess X x D (τ ω) ω)
    (le_refl (0 : ℝ)) (le_of_lt hy) hcap
  linarith
