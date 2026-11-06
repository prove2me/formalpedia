-- Prove2me | solution 1 for AvramDividend.Classical.avram_ubv_hor3_original_positive_ruin_initial_condexp_zero_masked_integral
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-05T18:30:36.386472+00:00
-- url     : https://prove2.me/submissions/de0e1a84-cf77-4009-8a7a-3070ee13a662

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_ubv_hor3_original_zero_ruin_event_rightcont_initial_measurable
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (C : ℝ≥0∞)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (M : Ω → ℝ) (hMI : Integrable M P)
    (hCondZero : ∀ᵐ ω ∂P,
      condExp (𝓕.rightCont 0) P M ω = 0) :
    (∫ ω in {ω : Ω | ruinTime X x D ω ≠ 0}, M ω ∂P) = 0 := by
  letI : IsProbabilityMeasure P := X.isProbability
  have hm : (𝓕.rightCont 0) ≤ mΩ := (𝓕.rightCont).le 0
  haveI : SigmaFinite (P.trim hm) := inferInstance
  have hEvent :=
    (avram_ubv_hor3_original_zero_ruin_event_rightcont_initial_measurable
      X x C D hD).2
  have hCondRestrict :
      ∀ᵐ ω ∂P.restrict {ω : Ω | ruinTime X x D ω ≠ 0},
        condExp (𝓕.rightCont 0) P M ω = 0 :=
    ae_restrict_of_ae hCondZero
  have hSetIntegral :=
    setIntegral_condExp hm hMI hEvent
  calc
    (∫ ω in {ω : Ω | ruinTime X x D ω ≠ 0}, M ω ∂P) =
      (∫ ω in {ω : Ω | ruinTime X x D ω ≠ 0},
        condExp (𝓕.rightCont 0) P M ω ∂P) := hSetIntegral.symm
    _ = 0 := by
      rw [integral_congr_ae hCondRestrict]
      simp
