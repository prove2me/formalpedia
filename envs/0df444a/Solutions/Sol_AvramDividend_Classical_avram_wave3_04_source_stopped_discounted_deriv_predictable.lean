-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave3_04_source_stopped_discounted_deriv_predictable
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-30T13:49:19.010066+00:00
-- url     : https://prove2.me/submissions/1ed7f56b-ad3d-428f-93d1-2be40dc6ae57

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave3_04_postPaymentReserve_leftLim_stronglyPredictable
import Theorems.Thm_AvramDividend_Classical_avram_wave3_04_discounted_deriv_stronglyPredictable
import Theorems.Thm_AvramDividend_Classical_avram_wave3_04_stronglyPredictable_inclusive_horizon
import Theorems.Thm_AvramDividend_Classical_avram_wave3_04_inclusiveSurvival_stronglyPredictable
import Theorems.Thm_AvramDividend_Classical_ruinTime_stopping_rightCont_filtration

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter Set Topology AvramDividend.Classical
open scoped NNReal ENNReal

/-- The exact original controlled Lévy reserve's discounted derivative,
killed inclusively at ruin and finite horizon, is strongly predictable. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (hD : IsDividendStrategy 𝓕 D)
    (w : ℝ → ℝ) (q : ℝ) (T : ℝ≥0) :
    IsStronglyPredictable 𝓕.rightCont
      (fun t ω =>
        if t ≤ T then
          (Real.exp (-(q * (t : ℝ))) *
            deriv w (Function.leftLim
              (fun s : ℝ≥0 => x + X.X s ω - rightLimit D s ω) t)) *
          (if (t : ℝ≥0∞) ≤ ruinTime X x D ω then (1 : ℝ) else 0)
        else 0) := by
  have hReserve :=
    avram_wave3_04_postPaymentReserve_leftLim_stronglyPredictable X x D hD
  have hDisc := avram_wave3_04_discounted_deriv_stronglyPredictable
    (fun t ω => Function.leftLim
      (fun s : ℝ≥0 => x + X.X s ω - rightLimit D s ω) t)
    hReserve w q
  have hStop := ruinTime_stopping_rightCont_filtration X x D hD
  have hSurvive :=
    avram_wave3_04_inclusiveSurvival_stronglyPredictable
      (ruinTime X x D) hStop
  exact avram_wave3_04_stronglyPredictable_inclusive_horizon
    (fun t ω =>
      (Real.exp (-(q * (t : ℝ))) *
        deriv w (Function.leftLim
          (fun s : ℝ≥0 => x + X.X s ω - rightLimit D s ω) t)) *
      (if (t : ℝ≥0∞) ≤ ruinTime X x D ω then (1 : ℝ) else 0))
    (hDisc.mul hSurvive) T
