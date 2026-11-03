-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave6_10_original_qpos_common_esscher_bounded_random_horizon_cash_bound
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-02T09:06:07.526747+00:00
-- url     : https://prove2.me/submissions/27a518c8-de8b-4dd6-9f16-7f031ec2cf8d

import Mathlib.Analysis.Complex.Exponential
import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave6_10_original_qpos_common_esscher_every_real_horizon_each_admissible_cash_bound

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

/-- The same source Esscher exponent controls payouts up to any samplewise
    bounded random real cutoff, preserving the terminal and time-zero atoms. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (q : ℝ) (hq : 0 < q) :
    ∃ θ : ℝ, 0 < θ ∧ ∀ R x : ℝ, x ≤ R →
      ∀ C : ℝ≥0∞, ∀ D : ℝ≥0 → Ω → ℝ,
        IsAdmissibleLe X x C D →
      ∀ T : ℝ, ∀ τ : Ω → ℝ, (∀ ω, τ ω ≤ T) →
        ENNReal.ofReal θ *
          (∫⁻ ω, ∫⁻ t in
            paymentTimes (ruinTime X x D ω) ∩ Iic (τ ω),
            ENNReal.ofReal (Real.exp (-(q * t)))
              ∂(dividendMeasure D ω) ∂P) ≤
          ENNReal.ofReal (Real.exp (θ * R)) := by
  obtain ⟨θ, hθ, hdet⟩ :=
    avram_wave6_10_original_qpos_common_esscher_every_real_horizon_each_admissible_cash_bound
      X q hq
  refine ⟨θ, hθ, ?_⟩
  intro R x hx C D hD T τ hτ
  have hsub (ω : Ω) :
      paymentTimes (ruinTime X x D ω) ∩ Iic (τ ω) ⊆
        paymentTimes (ruinTime X x D ω) ∩ Iic T := by
    rintro t ⟨htpay, htτ⟩
    exact ⟨htpay, htτ.trans (hτ ω)⟩
  have hmono (ω : Ω) :
      (∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iic (τ ω),
        ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)) ≤
      (∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iic T,
        ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)) :=
    MeasureTheory.lintegral_mono_set (hsub ω)
  calc
    ENNReal.ofReal θ *
        (∫⁻ ω, ∫⁻ t in
          paymentTimes (ruinTime X x D ω) ∩ Iic (τ ω),
          ENNReal.ofReal (Real.exp (-(q * t)))
            ∂(dividendMeasure D ω) ∂P) ≤
        ENNReal.ofReal θ *
          (∫⁻ ω, ∫⁻ t in
            paymentTimes (ruinTime X x D ω) ∩ Iic T,
            ENNReal.ofReal (Real.exp (-(q * t)))
              ∂(dividendMeasure D ω) ∂P) :=
      mul_le_mul_of_nonneg_left (MeasureTheory.lintegral_mono hmono) bot_le
    _ ≤ ENNReal.ofReal (Real.exp (θ * R)) :=
      hdet R x hx C D hD T
