-- Prove2me | solution 1 for AvramDividend.Classical.avram_bva_a66_original_strict_prehorizon_cash_prepayment_reward_measurable
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-14T00:05:31.35136+00:00
-- url     : https://prove2.me/submissions/cb52f9e1-5b31-4e0b-92c3-67f2c77e38d9

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_p3_bv_original_strict_cash_measurable
import Theorems.Thm_AvramDividend_Classical_ruinTime_measurable
import Theorems.Thm_AvramDividend_Classical_avram_p3_g2_original_prepayment_riskProcess_joint_measurable
import Theorems.Thm_AvramDividend_Classical_local_verification_candidate_borel_and_postPayment_adapted
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (x : ℝ)
    (C : ℝ≥0∞) (D : ℝ≥0 → Ω → ℝ)
    (hD : IsAdmissibleLe X x C D)
    (w : ℝ → ℝ) (hw_cont : ContinuousOn w (Ici 0))
    (hw_neg : ∀ y < 0, w y = 0)
    (q : ℝ) (r : ℝ≥0) :
    Measurable (fun ω : Ω => ENNReal.ofReal
      ((∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iio (r : ℝ),
        ENNReal.ofReal (Real.exp (-(q * t)))
          ∂(dividendMeasure D ω)).toReal +
       (if (r : ℝ≥0∞) < ruinTime X x D ω then
          Real.exp (-(q * (r : ℝ))) * w (riskProcess X x D r ω)
        else 0))) := by
  have hDiv : IsDividendStrategy 𝓕 D := hD.1.1
  have hRuin : Measurable (ruinTime X x D) :=
    ruinTime_measurable X x D hDiv
  have hCash : Measurable (fun ω : Ω =>
      (∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iio (r : ℝ),
        ENNReal.ofReal (Real.exp (-(q * t)))
          ∂(dividendMeasure D ω)).toReal) :=
    (avram_p3_bv_original_strict_cash_measurable
      D hDiv (ruinTime X x D) hRuin q (r : ℝ)).ennreal_toReal
  have hPair : Measurable (fun ω : Ω => (r, ω)) :=
    measurable_const.prodMk measurable_id
  have hRisk : Measurable (fun ω : Ω => riskProcess X x D r ω) := by
    simpa only [Function.comp_def] using
      (avram_p3_g2_original_prepayment_riskProcess_joint_measurable
        X x D hDiv).comp hPair
  have hwMeas : Measurable w :=
    (local_verification_candidate_borel_and_postPayment_adapted
      X x D hDiv w hw_cont hw_neg).1
  have hSurv : MeasurableSet
      {ω : Ω | (r : ℝ≥0∞) < ruinTime X x D ω} :=
    measurableSet_lt measurable_const hRuin
  have hTerm : Measurable (fun ω : Ω =>
      if (r : ℝ≥0∞) < ruinTime X x D ω then
        Real.exp (-(q * (r : ℝ))) * w (riskProcess X x D r ω)
      else 0) :=
    Measurable.ite hSurv
      (measurable_const.mul (hwMeas.comp hRisk)) measurable_const
  exact ENNReal.measurable_ofReal.comp (hCash.add hTerm)
