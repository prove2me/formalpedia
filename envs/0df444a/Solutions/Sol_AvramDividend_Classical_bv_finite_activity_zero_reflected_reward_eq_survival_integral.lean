-- Prove2me | solution 1 for AvramDividend.Classical.bv_finite_activity_zero_reflected_reward_eq_survival_integral
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-26T21:18:21.986056+00:00
-- url     : https://prove2.me/submissions/3444dbd1-8623-433c-85d8-6263d33f166e

import Theorems.Thm_AvramDividend_Classical_bv_zero_stopped_reward_eq_drift_volume_ae_unconditional
import Theorems.Thm_AvramDividend_Classical_paymentTimes_lintegral_smul_volume
import Theorems.Thm_AvramDividend_Classical_paymentTimes_volume_lintegral_eq_strict_survival
import Theorems.Thm_AvramDividend_Classical_bv_finite_activity_discounted_survival_lintegral_eq_real
import Theorems.Thm_AvramDividend_Classical_extended_ruin_strict_survival_tonelli
import Theorems.Thm_AvramDividend_Classical_barrierRuinTime_measurable
import Theorems.Thm_AvramDividend_Classical_bv_standing_drift_pos
import Mathlib.Tactic.FunProp
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal
/-- Pathwise drift identification and Tonelli give the exponential survival reward. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (q : ℝ) (hq : 0 < q) (hBV : X.BoundedVariation)
    (hFinite : X.ν (Iio (0 : ℝ)) < ⊤) :
    barrierSupValue X 0 q =
      ENNReal.ofReal
        (∫ t : ℝ in Ioi (0 : ℝ),
          X.drift * Real.exp (-(q + (X.ν (Iio (0 : ℝ))).toReal) * t)
            ∂volume) := by
  letI : IsProbabilityMeasure P := X.isProbability
  have hd : 0 ≤ X.drift := le_of_lt (bv_standing_drift_pos X hX hBV).1
  have hw : Measurable (fun t : ℝ => ENNReal.ofReal (Real.exp (-(q * t)))) := by
    fun_prop
  have hwd : Measurable
      (fun t : ℝ => ENNReal.ofReal (X.drift * Real.exp (-(q * t)))) := by
    fun_prop
  have hPath := bv_zero_stopped_reward_eq_drift_volume_ae_unconditional X hX hBV hFinite
  have hDensity (σ : ℝ≥0∞) :
      (∫⁻ t in paymentTimes σ,
        ENNReal.ofReal (Real.exp (-(q * t)))
          ∂((ENNReal.ofReal X.drift) • volume)) =
      (∫⁻ t in paymentTimes σ,
        ENNReal.ofReal (X.drift * Real.exp (-(q * t))) ∂volume) := by
    rw [paymentTimes_lintegral_smul_volume σ (ENNReal.ofReal X.drift) _ hw]
    apply lintegral_congr
    intro t
    simpa only [ENNReal.ofReal_mul hd]
  have hDet (σ : ℝ≥0∞) :
      (∫⁻ t in paymentTimes σ,
        ENNReal.ofReal (Real.exp (-(q * t)))
          ∂((ENNReal.ofReal X.drift) • volume)) =
      (∫⁻ t in Ioi (0 : ℝ),
        (if ENNReal.ofReal t < σ then
          ENNReal.ofReal (X.drift * Real.exp (-(q * t))) else 0)
          ∂volume) := by
    exact (hDensity σ).trans
      (paymentTimes_volume_lintegral_eq_strict_survival σ _)
  calc
    barrierSupValue X 0 q =
      (∫⁻ ω, ∫⁻ t in paymentTimes (barrierRuinTime X 0 ω),
        ENNReal.ofReal (Real.exp (-(q * t)))
          ∂(dividendMeasure (runningSup X) ω) ∂P) := rfl
    _ = (∫⁻ ω, ∫⁻ t in paymentTimes (barrierRuinTime X 0 ω),
        ENNReal.ofReal (Real.exp (-(q * t)))
          ∂((ENNReal.ofReal X.drift) • volume) ∂P) := by
      apply lintegral_congr_ae
      filter_upwards [hPath] with ω hω
      exact hω _
    _ = (∫⁻ ω, ∫⁻ t in Ioi (0 : ℝ),
        (if ENNReal.ofReal t < barrierRuinTime X 0 ω then
          ENNReal.ofReal (X.drift * Real.exp (-(q * t))) else 0)
          ∂volume ∂P) := by
      apply lintegral_congr
      intro ω
      exact hDet _
    _ = (∫⁻ t in Ioi (0 : ℝ),
        P {ω : Ω | ENNReal.ofReal t < barrierRuinTime X 0 ω} *
          ENNReal.ofReal (X.drift * Real.exp (-(q * t))) ∂volume) :=
      extended_ruin_strict_survival_tonelli P (barrierRuinTime X 0)
        (barrierRuinTime_measurable X 0) _ hwd
    _ = ENNReal.ofReal
      (∫ t : ℝ in Ioi (0 : ℝ),
        X.drift * Real.exp (-(q + (X.ν (Iio (0 : ℝ))).toReal) * t)
          ∂volume) :=
      bv_finite_activity_discounted_survival_lintegral_eq_real
        X hX q hq hBV hFinite
