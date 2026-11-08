-- Prove2me | solution 1 for AvramDividend.Classical.avram_ubv_finite9_original_F_family_integrable_envelope
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-07T10:02:10.737472+00:00
-- url     : https://prove2.me/submissions/c78beed2-a123-4d7a-aa28-7a4391760dca

import Mathlib.Probability.Process.Filtration
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_ubv_finite9_original_stopping_family_uniform_terminal_bound
import Theorems.Thm_AvramDividend_Classical_avram_p4_d_dividend_original_literal_stopped_payment_cash_lintegral_finite

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x q : ℝ) (hq : 0 ≤ q)
    (C : ℝ≥0∞) (hfinite : C ≠ ⊤)
    (hxc : ENNReal.ofReal x ≤ C)
    (w : ℝ → ℝ) (hw_cont : ContinuousOn w (Ici 0))
    (hw_neg : ∀ y < 0, w y = 0)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (τ : Ω → ℝ≥0)
    (hCashτI : Integrable
      (fun ω => (∫⁻ s in paymentTimes (ruinTime X x D ω) ∩ Iic (τ ω : ℝ),
        ENNReal.ofReal (Real.exp (-(q * s)))
        ∂(dividendMeasure D ω)).toReal) P)
    (σ : ℕ → Ω → ℝ≥0)
    (hσle : ∀ k ω, σ k ω ≤ τ ω)
    (F : ℕ → Ω → ℝ)
    (hFsource : ∀ k ω, F k ω =
      Real.exp (-(q * (σ k ω : ℝ))) *
        w (if σ k ω = 0 ∨
              (σ k ω : ℝ≥0∞) < ruinTime X x D ω then
            x + X.X (σ k ω) ω - rightLimit D (σ k ω) ω
          else riskProcess X x D (σ k ω) ω) +
      (∫⁻ s in paymentTimes (ruinTime X x D ω) ∩ Iic (σ k ω : ℝ),
        ENNReal.ofReal (Real.exp (-(q * s)))
        ∂(dividendMeasure D ω)).toReal) :
    ∃ B : ℝ, 0 ≤ B ∧
      (∀ k ω, |F k ω| ≤ B +
        (∫⁻ s in paymentTimes (ruinTime X x D ω) ∩ Iic (τ ω : ℝ),
          ENNReal.ofReal (Real.exp (-(q * s)))
          ∂(dividendMeasure D ω)).toReal) ∧
      Integrable (fun ω => B +
        (∫⁻ s in paymentTimes (ruinTime X x D ω) ∩ Iic (τ ω : ℝ),
          ENNReal.ofReal (Real.exp (-(q * s)))
          ∂(dividendMeasure D ω)).toReal) P := by
  classical
  letI : IsProbabilityMeasure P := X.isProbability
  let W : ℕ → Ω → ℝ := fun k ω =>
    if σ k ω = 0 ∨ (σ k ω : ℝ≥0∞) < ruinTime X x D ω then
      x + X.X (σ k ω) ω - rightLimit D (σ k ω) ω
    else riskProcess X x D (σ k ω) ω
  have hW : ∀ k ω, W k ω =
      if σ k ω = 0 ∨ (σ k ω : ℝ≥0∞) < ruinTime X x D ω then
        x + X.X (σ k ω) ω - rightLimit D (σ k ω) ω
      else riskProcess X x D (σ k ω) ω := by
    intros; rfl
  obtain ⟨B, hB, hbw⟩ :=
    avram_ubv_finite9_original_stopping_family_uniform_terminal_bound
      X x C hfinite hxc w hw_cont hw_neg D hD σ W hW
  refine ⟨B, hB, ?_, ?_⟩
  · intro k ω
    have ht : 0 ≤ (σ k ω : ℝ) := (σ k ω).property
    have hp : 0 ≤ q * (σ k ω : ℝ) := mul_nonneg hq ht
    have he : 0 ≤ Real.exp (-(q * (σ k ω : ℝ))) := Real.exp_nonneg _
    have he1 : Real.exp (-(q * (σ k ω : ℝ))) ≤ 1 := by
      apply Real.exp_le_one_iff.mpr
      linarith
    have hterm :
        Real.exp (-(q * (σ k ω : ℝ))) * |w (W k ω)| ≤ B := by
      calc
        _ ≤ |w (W k ω)| := by nlinarith [abs_nonneg (w (W k ω))]
        _ ≤ B := hbw k ω
    have hclock : (σ k ω : ℝ) ≤ (τ ω : ℝ) := by
      exact_mod_cast hσle k ω
    have hcashENN :
        (∫⁻ s in paymentTimes (ruinTime X x D ω) ∩ Iic (σ k ω : ℝ),
          ENNReal.ofReal (Real.exp (-(q * s)))
          ∂(dividendMeasure D ω)) ≤
        (∫⁻ s in paymentTimes (ruinTime X x D ω) ∩ Iic (τ ω : ℝ),
          ENNReal.ofReal (Real.exp (-(q * s)))
          ∂(dividendMeasure D ω)) := by
      apply lintegral_mono_set
      intro t ht
      exact ⟨ht.1, le_trans ht.2 hclock⟩
    have hCashFinite :=
      avram_p4_d_dividend_original_literal_stopped_payment_cash_lintegral_finite
        D hD.1.1 ω (ruinTime X x D ω) (τ ω) q hq
    have hcashle := ENNReal.toReal_mono (ne_of_lt hCashFinite) hcashENN
    have hcashnn : 0 ≤
        (∫⁻ s in paymentTimes (ruinTime X x D ω) ∩ Iic (σ k ω : ℝ),
          ENNReal.ofReal (Real.exp (-(q * s)))
          ∂(dividendMeasure D ω)).toReal := ENNReal.toReal_nonneg
    calc
      |F k ω| =
          |Real.exp (-(q * (σ k ω : ℝ))) * w (W k ω) +
            (∫⁻ s in paymentTimes (ruinTime X x D ω) ∩ Iic (σ k ω : ℝ),
              ENNReal.ofReal (Real.exp (-(q * s)))
              ∂(dividendMeasure D ω)).toReal| := by
          rw [hFsource k ω]
      _ ≤ |Real.exp (-(q * (σ k ω : ℝ))) * w (W k ω)| +
          |(∫⁻ s in paymentTimes (ruinTime X x D ω) ∩ Iic (σ k ω : ℝ),
              ENNReal.ofReal (Real.exp (-(q * s)))
              ∂(dividendMeasure D ω)).toReal| := abs_add_le _ _
      _ = Real.exp (-(q * (σ k ω : ℝ))) * |w (W k ω)| +
          (∫⁻ s in paymentTimes (ruinTime X x D ω) ∩ Iic (σ k ω : ℝ),
              ENNReal.ofReal (Real.exp (-(q * s)))
              ∂(dividendMeasure D ω)).toReal := by
          rw [abs_mul, abs_of_nonneg he, abs_of_nonneg hcashnn]
      _ ≤ B + (∫⁻ s in paymentTimes (ruinTime X x D ω) ∩ Iic (τ ω : ℝ),
              ENNReal.ofReal (Real.exp (-(q * s)))
              ∂(dividendMeasure D ω)).toReal := by linarith
  · exact (integrable_const B).add hCashτI
