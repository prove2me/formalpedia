-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave7_03_original_real_toReal_cash_mean_eq_signed_stieltjes_mean
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-02T13:32:17.97117+00:00
-- url     : https://prove2.me/submissions/9424275f-90b9-4a2f-94c0-2eb13915222e

import Mathlib.Analysis.Complex.Exponential
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave7_03_original_full_ruin_finite_horizon_real_ennreal_eq
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true
open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical
noncomputable section

/-- Original expected real cash computed from the ENNReal payout's toReal
    agrees with the genuine signed real Stieltjes expectation on the same set. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (C : ℝ≥0∞)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (q : ℝ) (hq : 0 ≤ q) (T : ℝ) (hT : 0 ≤ T) :
    (∫ ω, (∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iic T,
      ENNReal.ofReal (Real.exp (-(q * t)))
        ∂(dividendMeasure D ω)).toReal ∂P) =
    (∫ ω, (∫ t in paymentTimes (ruinTime X x D ω) ∩ Iic T,
      Real.exp (-(q * t)) ∂(dividendMeasure D ω)) ∂P) := by
  have hDiv : IsDividendStrategy 𝓕 D := hD.1.1
  apply integral_congr_ae
  apply Filter.Eventually.of_forall
  intro ω
  have hPath := avram_wave7_03_original_full_ruin_finite_horizon_real_ennreal_eq
    X x D hDiv ω T.toNNReal q hq
  rw [Real.coe_toNNReal T hT] at hPath
  have hg : 0 ≤
      (∫ t in paymentTimes (ruinTime X x D ω) ∩ Iic T,
        Real.exp (-(q * t)) ∂(dividendMeasure D ω)) := by
    apply integral_nonneg
    intro t
    exact (Real.exp_pos (-(q * t))).le
  calc
    (∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iic T,
      ENNReal.ofReal (Real.exp (-(q * t)))
        ∂(dividendMeasure D ω)).toReal =
      (ENNReal.ofReal (∫ t in paymentTimes (ruinTime X x D ω) ∩ Iic T,
        Real.exp (-(q * t)) ∂(dividendMeasure D ω))).toReal :=
          congrArg ENNReal.toReal hPath
    _ = _ := ENNReal.toReal_ofReal hg
