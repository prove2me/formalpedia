-- Prove2me | solution 1 for AvramDividend.Classical.avram_gledger103_original_bounded_ruinclipped_strict_mass_L1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-11T12:49:26.916301+00:00
-- url     : https://prove2.me/submissions/1fb065af-32e5-4f44-959d-904635006eec

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_gledger98_original_random_strict_open_mass_measurable
import Theorems.Thm_AvramDividend_Classical_avram_gledger100_original_strict_real_mass_le_discounted_cash
import Theorems.Thm_AvramDividend_Classical_avram_gledger101_original_strict_clipped_clock_payment_support
import Theorems.Thm_AvramDividend_Classical_avram_ubv_gauss13_endpoint_original_uniform_measurable_strict_cash_envelope
import Theorems.Thm_AvramDividend_Classical_avram_p4_d_dividend_original_literal_stopped_payment_cash_lintegral_finite
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- Finite discounted pre-ruin cash dominates the original unweighted strict cash mass. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (x : ℝ) (C : ℝ≥0∞)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (q : ℝ) (hq : 0 ≤ q) (n : ℝ≥0)
    (ρ : Ω → ℝ≥0) (hρmeas : Measurable ρ)
    (hρbound : ∀ ω, ρ ω ≤ n)
    (hρruin : ∀ ω, (ρ ω : ℝ≥0∞) ≤ ruinTime X x D ω) :
    Integrable (fun ω : Ω =>
      (dividendMeasure D ω (Ioo (0 : ℝ) (ρ ω : ℝ))).toReal) P := by
  let F : Ω → ℝ := fun ω =>
    (∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iio (ρ ω : ℝ),
      ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)).toReal
  let M : Ω → ℝ := fun ω =>
    (dividendMeasure D ω (Ioo (0 : ℝ) (ρ ω : ℝ))).toReal
  change Integrable M P
  have hFI : Integrable F P := by
    obtain ⟨_, hstrict, _⟩ :=
      avram_ubv_gauss13_endpoint_original_uniform_measurable_strict_cash_envelope
        X x C D hD q hq n (fun _ => ρ)
        (by intro k; exact hρmeas.coe_nnreal_real)
        (by intro k ω; exact hρbound ω)
    exact hstrict 0
  have hMMeas : Measurable M :=
    ENNReal.measurable_toReal.comp
      (avram_gledger98_original_random_strict_open_mass_measurable
        D hD.1.1 ρ hρmeas)
  have hbound (ω : Ω) : M ω ≤ Real.exp (q * (n : ℝ)) * F ω := by
    have hρn : (ρ ω : ℝ) ≤ (n : ℝ) := by exact_mod_cast hρbound ω
    have hfinite : (∫⁻ t in paymentTimes (ruinTime X x D ω) ∩
        Iio (ρ ω : ℝ), ENNReal.ofReal (Real.exp (-(q * t)))
        ∂(dividendMeasure D ω)) < ⊤ := by
      have hclosed :=
        avram_p4_d_dividend_original_literal_stopped_payment_cash_lintegral_finite
          D hD.1.1 ω (ruinTime X x D ω) n q hq
      have hsets : paymentTimes (ruinTime X x D ω) ∩ Iio (ρ ω : ℝ) ⊆
          paymentTimes (ruinTime X x D ω) ∩ Iic (n : ℝ) := by
        intro t ht
        exact ⟨ht.1, le_trans (le_of_lt ht.2) hρn⟩
      exact lt_of_le_of_lt (lintegral_mono_set hsets) hclosed
    have hmass := avram_gledger100_original_strict_real_mass_le_discounted_cash
      (dividendMeasure D ω) (ruinTime X x D ω) q hq (ρ ω)
      (avram_gledger101_original_strict_clipped_clock_payment_support
        (ruinTime X x D ω) (ρ ω) (hρruin ω)) hfinite
    have he : Real.exp (q * (ρ ω : ℝ)) ≤ Real.exp (q * (n : ℝ)) :=
      Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hρn hq)
    exact hmass.trans (mul_le_mul_of_nonneg_right he ENNReal.toReal_nonneg)
  have hdom : Integrable (fun ω => Real.exp (q * (n : ℝ)) * F ω) P :=
    hFI.const_mul _
  apply hdom.mono' hMMeas.aestronglyMeasurable
  filter_upwards [] with ω
  have hm0 : 0 ≤ M ω := ENNReal.toReal_nonneg
  have hf0 : 0 ≤ F ω := ENNReal.toReal_nonneg
  have hg0 : 0 ≤ Real.exp (q * (n : ℝ)) * F ω :=
    mul_nonneg (le_of_lt (Real.exp_pos _)) hf0
  simpa only [Real.norm_eq_abs, abs_of_nonneg hm0,
    abs_of_nonneg hg0] using hbound ω
