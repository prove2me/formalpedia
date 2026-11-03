-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave7_03_original_real_horizon_ennreal_fibre_toReal_mean_eq_signed_stieltjes_mean
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-02T17:02:35.830367+00:00
-- url     : https://prove2.me/submissions/7e022bc0-480e-40e1-a1e2-e456840b19eb

import Mathlib.Analysis.Complex.Exponential
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave7_03_original_real_horizon_pathwise_full_stieltjes_eq
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true
open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical
noncomputable section

/-- At a finite real horizon, the source ENNReal fibre payout
    converted toReal equals the genuine signed Stieltjes fibre
    payout in the original outer real expectation, including t=0. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ)
    (D : ℝ≥0 → Ω → ℝ) (hDiv : IsDividendStrategy 𝓕 D)
    (q : ℝ) (hq : 0 ≤ q)
    (T : ℝ) (hT : 0 ≤ T) :
    (∫ ω, (∫⁻ t in
        paymentTimes (ruinTime X x D ω) ∩ Iic T,
      ENNReal.ofReal (Real.exp (-(q * t)))
        ∂(dividendMeasure D ω)).toReal ∂P) =
    (∫ ω, (∫ t in
        paymentTimes (ruinTime X x D ω) ∩ Iic T,
      Real.exp (-(q * t)) ∂(dividendMeasure D ω)) ∂P) := by
  have hFibre (ω : Ω) :
      (∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iic T,
        ENNReal.ofReal (Real.exp (-(q * t)))
          ∂(dividendMeasure D ω)).toReal =
      (∫ t in paymentTimes (ruinTime X x D ω) ∩ Iic T,
        Real.exp (-(q * t)) ∂(dividendMeasure D ω)) := by
    rw [avram_wave7_03_original_real_horizon_pathwise_full_stieltjes_eq
      X x D hDiv ω T hT q hq]
    apply ENNReal.toReal_ofReal
    apply integral_nonneg
    intro t
    exact (Real.exp_pos (-(q * t))).le
  apply integral_congr_ae
  exact Filter.Eventually.of_forall hFibre
