-- Prove2me | solution 1 for AvramDividend.Classical.avram_integration_sweep9_original_controlled_prestate_ambient_measurable
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-04T15:33:15.164972+00:00
-- url     : https://prove2.me/submissions/aff4f779-cdf4-45e1-ba2b-ac29ec2ecef3

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave3_04_postPaymentReserve_leftLim_stronglyPredictable
import Theorems.Thm_AvramDividend_Classical_avram_p3_e_compensator_original_rightCont_predictable_ambient_measurable
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
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (hD : IsDividendStrategy 𝓕 D) :
    Measurable (fun p : ℝ≥0 × Ω =>
      Function.leftLim
        (fun v : ℝ≥0 => x + X.X v p.2 - rightLimit D v p.2) p.1) := by
  let Y : ℝ≥0 × Ω → ℝ := fun p =>
    Function.leftLim
      (fun v : ℝ≥0 => x + X.X v p.2 - rightLimit D v p.2) p.1
  have hPred : IsStronglyPredictable 𝓕.rightCont
      (fun t ω => Function.leftLim
        (fun v : ℝ≥0 => x + X.X v ω - rightLimit D v ω) t) :=
    avram_wave3_04_postPaymentReserve_leftLim_stronglyPredictable X x D hD
  change Measurable Y
  intro s hs
  have hPredSet :
      MeasurableSet[𝓕.rightCont.predictable] (Y ⁻¹' s) := by
    letI : MeasurableSpace (ℝ≥0 × Ω) := 𝓕.rightCont.predictable
    have hm : Measurable Y :=
      (show StronglyMeasurable Y from hPred).measurable
    exact hm hs
  exact avram_p3_e_compensator_original_rightCont_predictable_ambient_measurable
    (Y ⁻¹' s) hPredSet

