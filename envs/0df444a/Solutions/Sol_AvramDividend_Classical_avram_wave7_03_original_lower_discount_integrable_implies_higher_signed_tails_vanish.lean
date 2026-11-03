-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave7_03_original_lower_discount_integrable_implies_higher_signed_tails_vanish
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-02T23:55:55.011717+00:00
-- url     : https://prove2.me/submissions/89cd63b4-fd19-454a-9901-869eff54ac21

import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Mathlib.Analysis.Complex.Exponential
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_paymentTimes_measurable
import Theorems.Thm_AvramDividend_Classical_avram_wave7_03_pathwise_original_full_cash_finite_iff_signed_stieltjes_integrable
import Theorems.Thm_AvramDividend_Classical_avram_wave7_03_original_unrestricted_integrable_signed_stieltjes_tail_tendsto_zero
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true
open MeasureTheory Set Filter Topology
open scoped NNReal ENNReal
open AvramDividend.Classical
noncomputable section

/-- Genuine signed source-integrability at a lower rate makes all stronger
    discounted strict future Stieltjes payout tails vanish on the same path. -/
/- Recovered original-process signed-tail transport after terminal proof-storage failure. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (hD : IsDividendStrategy 𝓕 D)
    (ω : Ω) (q₁ q₂ : ℝ) (hq : q₁ ≤ q₂)
    (hInt : IntegrableOn (fun t : ℝ => Real.exp (-(q₁ * t)))
      (paymentTimes (ruinTime X x D ω)) (dividendMeasure D ω)) :
    Tendsto (fun n : ℕ =>
      ∫ t in paymentTimes (ruinTime X x D ω) ∩ Ioi (n : ℝ),
        Real.exp (-(q₂ * t)) ∂(dividendMeasure D ω))
      atTop (𝓝 0) := by
  have hcash1 :
      (∫⁻ t in paymentTimes (ruinTime X x D ω),
        ENNReal.ofReal (Real.exp (-(q₁ * t)))
          ∂(dividendMeasure D ω)) < ⊤ :=
    (avram_wave7_03_pathwise_original_full_cash_finite_iff_signed_stieltjes_integrable
      X x D hD ω q₁).2 hInt
  have hcomp :
      (∫⁻ t in paymentTimes (ruinTime X x D ω),
        ENNReal.ofReal (Real.exp (-(q₂ * t)))
          ∂(dividendMeasure D ω)) ≤
      (∫⁻ t in paymentTimes (ruinTime X x D ω),
        ENNReal.ofReal (Real.exp (-(q₁ * t)))
          ∂(dividendMeasure D ω)) := by
    have hs : MeasurableSet (paymentTimes (ruinTime X x D ω)) :=
      paymentTimes_measurable (ruinTime X x D ω)
    apply lintegral_mono_ae
    filter_upwards [ae_restrict_mem hs] with t ht
    have hmul : q₁ * t ≤ q₂ * t :=
      mul_le_mul_of_nonneg_right hq ht.1
    exact ENNReal.ofReal_le_ofReal
      (Real.exp_le_exp.mpr (neg_le_neg hmul))
  have hcash2 :
      (∫⁻ t in paymentTimes (ruinTime X x D ω),
        ENNReal.ofReal (Real.exp (-(q₂ * t)))
          ∂(dividendMeasure D ω)) < ⊤ :=
    lt_of_le_of_lt hcomp hcash1
  exact
    avram_wave7_03_original_unrestricted_integrable_signed_stieltjes_tail_tendsto_zero
      X x D ω q₂
      ((avram_wave7_03_pathwise_original_full_cash_finite_iff_signed_stieltjes_integrable
        X x D hD ω q₂).1 hcash2)
