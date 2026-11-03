-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave7_03_finite_original_dividendValue_toReal_eq_expected_genuine_unrestricted_signed_cash
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-02T18:59:57.5479+00:00
-- url     : https://prove2.me/submissions/53c3fb8c-5f9a-4fce-b921-406d632b90ee

import Mathlib.Analysis.Complex.Exponential
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave7_03_original_perpetual_signed_stieltjes_L1_and_exact_outer_mean_of_finite
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true
open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical
noncomputable section

/-- The finite canonical original ENNReal perpetual dividend value
    converts exactly to the expected actual unrestricted real Stieltjes
    payout, with no time-zero or continuous dividend term omitted. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (hD : IsDividendStrategy 𝓕 D) (q : ℝ)
    (hFinite : dividendValue X q x D < ⊤) :
    (dividendValue X q x D).toReal =
      (∫ ω, (∫ t in paymentTimes (ruinTime X x D ω),
        Real.exp (-(q * t)) ∂(dividendMeasure D ω)) ∂P) := by
  have hMeanEq :=
    (avram_wave7_03_original_perpetual_signed_stieltjes_L1_and_exact_outer_mean_of_finite
      X x D hD q hFinite).2
  rw [hMeanEq]
  apply ENNReal.toReal_ofReal
  apply integral_nonneg
  intro ω
  apply integral_nonneg
  intro t
  exact (Real.exp_pos (-(q * t))).le
