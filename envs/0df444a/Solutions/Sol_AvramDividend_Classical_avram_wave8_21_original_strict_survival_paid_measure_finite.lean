-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave8_21_original_strict_survival_paid_measure_finite
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-02T23:44:59.562046+00:00
-- url     : https://prove2.me/submissions/056e5d53-66c6-43e8-8d14-f78d174fa94c

import Mathlib.Data.ENNReal.Basic
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave8_21_original_strict_survival_full_paid_measure_eq_rightLimit
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical
noncomputable section

/-- Full strictly stopped original Stieltjes payout mass is finite, including zero, the horizon right atom and all diffuse payout. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (x : ℝ)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (ω : Ω) (T : ℝ≥0)
    (hstrict : (T : ℝ≥0∞) < ruinTime X x D ω) :
    dividendMeasure D ω
      (paymentTimes (ruinTime X x D ω) ∩ Iic (T : ℝ)) < ⊤ := by
  rw [avram_wave8_21_original_strict_survival_full_paid_measure_eq_rightLimit
    X x D hD ω T hstrict]
  exact ENNReal.ofReal_lt_top
