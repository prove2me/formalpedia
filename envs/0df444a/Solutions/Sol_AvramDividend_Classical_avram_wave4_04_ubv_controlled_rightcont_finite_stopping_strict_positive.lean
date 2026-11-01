-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave4_04_ubv_controlled_rightcont_finite_stopping_strict_positive
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-31T16:35:08.324608+00:00
-- url     : https://prove2.me/submissions/24c939b6-b48f-4d26-8edf-6f3fc609c690

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_levy_rightCont_process
import Theorems.Thm_AvramDividend_Classical_dividendStrategy_rightCont_filtration
import Theorems.Thm_AvramDividend_Classical_riskProcess_nonnegative_strictly_before_ruin
import Theorems.Thm_AvramDividend_Classical_avram_wave4_04_ubv_original_controlled_preruin_finite_stopping_strict_positive

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal

/-!
The stopped control belongs to the same original sample space after the
right-continuous filtration transport. The identical sample path/triplet
is essential: no independent copy of X or marginal-law replacement is used.
-/

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hBV : ¬ X.BoundedVariation)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (hD : IsDividendStrategy 𝓕 D)
    (τ : Ω → ℝ≥0)
    (hτ : ∀ s : ℝ≥0,
      MeasurableSet[𝓕.rightCont s] {ω : Ω | τ ω ≤ s})
    (hstop : IsStoppingTime 𝓕.rightCont
      (fun ω => (τ ω : WithTop ℝ≥0))) :
    ∀ᵐ ω ∂P, ((τ ω : ℝ≥0) : ℝ≥0∞) < ruinTime X x D ω →
      0 < riskProcess X x D (τ ω) ω := by
  obtain ⟨Y, hXY, hc, hσ, hν⟩ := levy_rightCont_process X
  have hBVY : ¬ Y.BoundedVariation := by
    intro h
    apply hBV
    simpa only [SpectrallyNegativeLevy.BoundedVariation, hσ, hν] using h
  have hDY : IsDividendStrategy 𝓕.rightCont D :=
    dividendStrategy_rightCont_filtration D hD
  have hPreY : ∀ ω (s : ℝ≥0),
      (s : ℝ≥0∞) < ruinTime Y x D ω →
        0 ≤ riskProcess Y x D s ω := by
    intro ω s hs
    exact riskProcess_nonnegative_strictly_before_ruin Y x D ω s hs
  have hPositive :=
    avram_wave4_04_ubv_original_controlled_preruin_finite_stopping_strict_positive
      Y hBVY x D hDY hPreY τ hτ hstop
  simpa only [riskProcess, ruinTime, hXY] using hPositive
