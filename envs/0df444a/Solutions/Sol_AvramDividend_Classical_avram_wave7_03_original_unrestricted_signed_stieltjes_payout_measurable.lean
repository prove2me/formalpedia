-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave7_03_original_unrestricted_signed_stieltjes_payout_measurable
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-02T18:49:22.729213+00:00
-- url     : https://prove2.me/submissions/9bd9ed55-3832-45e4-8c4a-a16e88e4d96e

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave6_08_original_perpetual_stieltjes_cash_measurable
import Theorems.Thm_AvramDividend_Classical_avram_wave7_03_unrestricted_original_signed_stieltjes_eq_cash_toReal_pointwise
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true
open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical
noncomputable section

/-- The actual unrestricted original real Stieltjes payout is
    measurable, including on nonintegrable paths with Mathlib's convention. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (hD : IsDividendStrategy 𝓕 D) (q : ℝ) :
    Measurable (fun ω : Ω =>
      ∫ t in paymentTimes (ruinTime X x D ω),
        Real.exp (-(q * t)) ∂(dividendMeasure D ω)) := by
  let F : Ω → ℝ≥0∞ := fun ω =>
    ∫⁻ t in paymentTimes (ruinTime X x D ω),
      ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)
  let g : Ω → ℝ := fun ω =>
    ∫ t in paymentTimes (ruinTime X x D ω),
      Real.exp (-(q * t)) ∂(dividendMeasure D ω)
  have hFm : Measurable F :=
    avram_wave6_08_original_perpetual_stieltjes_cash_measurable
      X x D hD q
  have hEq : g = fun ω => (F ω).toReal := by
    funext ω
    exact (avram_wave7_03_unrestricted_original_signed_stieltjes_eq_cash_toReal_pointwise
      X x D hD ω q).symm
  change Measurable g
  rw [hEq]
  exact ENNReal.measurable_toReal.comp hFm
