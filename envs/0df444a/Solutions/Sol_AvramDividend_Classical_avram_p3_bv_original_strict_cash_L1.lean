-- Prove2me | solution 1 for AvramDividend.Classical.avram_p3_bv_original_strict_cash_L1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T12:33:09.24175+00:00
-- url     : https://prove2.me/submissions/165dc55d-0186-4c8d-abae-b0b95936cfb3

import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_p3_bv_original_strict_cash_measurable
import Theorems.Thm_AvramDividend_Classical_avram_p3_bv_closed_horizon_discounted_cash_split
import Theorems.Thm_AvramDividend_Classical_avram_wave5_03_original_real_horizon_full_stieltjes_reward_integrable_L1
import Theorems.Thm_AvramDividend_Classical_avram_wave7_03_original_full_ruin_finite_horizon_real_ennreal_eq
import Theorems.Thm_AvramDividend_Classical_paymentTimes_measurable
import Theorems.Thm_AvramDividend_Classical_ruinTime_measurable
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- The true original cash strictly before T is L1. The terminal right
dividend at T remains separate, and the time-zero atom remains included. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (C : ℝ≥0∞)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (q : ℝ) (hq : 0 ≤ q) (T : ℝ) (hT : 0 ≤ T) :
    Integrable (fun ω : Ω =>
      (∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iio T,
        ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)).toReal) P := by
  let F : Ω → ℝ≥0∞ := fun ω =>
    ∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iic T,
      ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)
  let G : Ω → ℝ≥0∞ := fun ω =>
    ∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iio T,
      ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)
  have hDiv : IsDividendStrategy 𝓕 D := hD.1.1
  have hGMeas : Measurable G := by
    simpa only [G] using
      (avram_p3_bv_original_strict_cash_measurable D hDiv
        (ruinTime X x D) (ruinTime_measurable X x D hDiv) q T)
  have hFInt : Integrable (fun ω => (F ω).toReal) P := by
    simpa only [F] using
      (avram_wave5_03_original_real_horizon_full_stieltjes_reward_integrable_L1
        X x C D hD T hT q)
  have hFFin (ω : Ω) : F ω ≠ ⊤ := by
    have h := avram_wave7_03_original_full_ruin_finite_horizon_real_ennreal_eq
      X x D hDiv ω (⟨T, hT⟩ : ℝ≥0) q hq
    change F ω = ENNReal.ofReal (∫ t in
      paymentTimes (ruinTime X x D ω) ∩ Iic T,
        Real.exp (-(q * t)) ∂(dividendMeasure D ω)) at h
    rw [h]
    exact ENNReal.ofReal_ne_top
  have hGF (ω : Ω) : G ω ≤ F ω := by
    change (∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iio T,
      ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)) ≤
      (∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iic T,
      ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω))
    rw [avram_p3_bv_closed_horizon_discounted_cash_split
      X x D q T ω (paymentTimes_measurable (ruinTime X x D ω))]
    exact le_add_of_nonneg_right zero_le
  exact hFInt.mono' hGMeas.ennreal_toReal.aestronglyMeasurable
    (Filter.Eventually.of_forall (fun ω => by
      simpa only [G, Real.norm_eq_abs,
        abs_of_nonneg ENNReal.toReal_nonneg] using
        ENNReal.toReal_mono (hFFin ω) (hGF ω)))
