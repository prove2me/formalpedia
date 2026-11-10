-- Prove2me | solution 1 for AvramDividend.Classical.avram_pj_reward19_original_rightcont_survival_stop_strict_positive
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-09T17:46:13.578907+00:00
-- url     : https://prove2.me/submissions/bd0787dd-902c-4938-9e7f-57180677a1d6

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave4_04_ubv_controlled_rightcont_finite_stopping_strict_positive

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hBV : ¬ X.BoundedVariation)
    (x : ℝ) (C : ℝ≥0∞) (D : ℝ≥0 → Ω → ℝ)
    (hD : IsAdmissibleLe X x C D)
    (ρ : Ω → ℝ≥0)
    (hρstop : IsStoppingTime 𝓕.rightCont
      (fun ω => (ρ ω : WithTop ℝ≥0))) :
    ∀ᵐ ω ∂P, (ρ ω : ℝ≥0∞) < ruinTime X x D ω →
      0 < riskProcess X x D (ρ ω) ω := by
  have hρ : ∀ s : ℝ≥0,
      MeasurableSet[𝓕.rightCont s] {ω : Ω | ρ ω ≤ s} := by
    intro s
    simpa only [WithTop.coe_le_coe] using (hρstop s)
  exact avram_wave4_04_ubv_controlled_rightcont_finite_stopping_strict_positive
    X hBV x D hD.1.1 ρ hρ hρstop
