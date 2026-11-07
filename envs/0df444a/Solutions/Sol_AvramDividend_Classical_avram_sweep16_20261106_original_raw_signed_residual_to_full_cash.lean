-- Prove2me | solution 1 for AvramDividend.Classical.avram_sweep16_20261106_original_raw_signed_residual_to_full_cash
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-06T07:47:34.884203+00:00
-- url     : https://prove2.me/submissions/29d692df-2282-41c3-9a99-2b6ac0dd94db

import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Complex.Exponential
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_ruinTime_measurable
import Theorems.Thm_AvramDividend_Classical_avram_wave7_08_actual_truncated_clock_real_measurable_of_source
import Theorems.Thm_AvramDividend_Classical_avram_wave6_08_original_bounded_random_clock_full_stieltjes_cash_integrable
import Theorems.Thm_AvramDividend_Classical_avram_p4_e_localise_original_exact_terminal_L1_from_source_signed_budget
import Theorems.Thm_AvramDividend_Classical_avram_sweep16_20261106_natural_ruin_clock_full_stopping_package
import Theorems.Thm_AvramDividend_Classical_avram_sweep16_20261106_natural_l1_residual_to_full_cash
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hBV : ¬ X.BoundedVariation)
    (q : ℝ) (hq : 0 < q) (w : ℝ → ℝ)
    (C : ℝ≥0∞) (hC : 0 < C)
    (hw0 : 0 ≤ w 0) (hw_cont : ContinuousOn w (Ici 0))
    (hw_neg : ∀ y : ℝ, y < 0 → w y = 0)
    (hw_smooth : ContDiffOn ℝ 2 w
      {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (hw_gen : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C →
      X.GeneratorIntegrable w y ∧ X.generator w y - q * w y ≤ 0)
    (hw_grad : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C → 1 ≤ deriv w y)
    (x : ℝ) (hx : 0 ≤ x) (hxc : ENNReal.ofReal x ≤ C)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (T : ℝ)
    (hRaw : ∀ n : ℕ, 0 < n → ∃ W Cash Term M G H : Ω → ℝ,
      (∀ ω, W ω = if (min (ruinTime X x D ω) (n : ℝ≥0∞)).toNNReal = 0 ∨
        (((min (ruinTime X x D ω) (n : ℝ≥0∞)).toNNReal : ℝ≥0) : ℝ≥0∞) <
          ruinTime X x D ω then
        x + X.X (min (ruinTime X x D ω) (n : ℝ≥0∞)).toNNReal ω -
          rightLimit D (min (ruinTime X x D ω) (n : ℝ≥0∞)).toNNReal ω
        else riskProcess X x D (min (ruinTime X x D ω) (n : ℝ≥0∞)).toNNReal ω) ∧
      (∀ ω, Cash ω =
        (∫⁻ t in paymentTimes (ruinTime X x D ω) ∩
            Iic (((min (ruinTime X x D ω) (n : ℝ≥0∞)).toNNReal : ℝ≥0) : ℝ),
          ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)).toReal) ∧
      (∀ ω, Term ω =
        Real.exp (-(q * (((min (ruinTime X x D ω) (n : ℝ≥0∞)).toNNReal : ℝ≥0) : ℝ))) *
          w (W ω)) ∧
      AEStronglyMeasurable Term P ∧
      Integrable M P ∧ Integrable G P ∧ Integrable H P ∧
      (∫ ω, M ω ∂P) = 0 ∧
      (∀ᵐ ω ∂P, G ω + H ω ≤ 0) ∧
      (∀ᵐ ω ∂P, Term ω + Cash ω ≤ w x + M ω + G ω + H ω)) :
    (∫⁻ ω, ∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iic T,
      ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω) ∂P) ≤
    ENNReal.ofReal (w x) := by
  have hClock :=
    avram_sweep16_20261106_natural_ruin_clock_full_stopping_package X x C D hD
  have hSmooth : (¬ X.BoundedVariation →
      ContDiffOn ℝ 2 w {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C}) ∧
      (X.BoundedVariation →
      ContDiffOn ℝ 1 w {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C}) := by
    refine ⟨fun _ => hw_smooth, ?_⟩
    intro hBV'
    exact False.elim (hBV hBV')
  have hRuinMeas : Measurable (ruinTime X x D) :=
    ruinTime_measurable X x D hD.1.1
  have hL1 : ∀ n : ℕ, 0 < n → ∃ W Cash Term M G H : Ω → ℝ,
      (∀ ω, W ω = if (min (ruinTime X x D ω) (n : ℝ≥0∞)).toNNReal = 0 ∨
        (((min (ruinTime X x D ω) (n : ℝ≥0∞)).toNNReal : ℝ≥0) : ℝ≥0∞) <
          ruinTime X x D ω then
        x + X.X (min (ruinTime X x D ω) (n : ℝ≥0∞)).toNNReal ω -
          rightLimit D (min (ruinTime X x D ω) (n : ℝ≥0∞)).toNNReal ω
        else riskProcess X x D (min (ruinTime X x D ω) (n : ℝ≥0∞)).toNNReal ω) ∧
      (∀ ω, Cash ω =
        (∫⁻ t in paymentTimes (ruinTime X x D ω) ∩
            Iic (((min (ruinTime X x D ω) (n : ℝ≥0∞)).toNNReal : ℝ≥0) : ℝ),
          ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)).toReal) ∧
      (∀ ω, Term ω =
        Real.exp (-(q * (((min (ruinTime X x D ω) (n : ℝ≥0∞)).toNNReal : ℝ≥0) : ℝ))) *
          w (W ω)) ∧
      Integrable Term P ∧ Integrable Cash P ∧
      Integrable M P ∧ Integrable G P ∧ Integrable H P ∧
      (∫ ω, M ω ∂P) = 0 ∧
      (∀ᵐ ω ∂P, G ω + H ω ≤ 0) ∧
      (∀ᵐ ω ∂P, Term ω + Cash ω ≤ w x + M ω + G ω + H ω) := by
    intro n hn
    rcases hRaw n hn with ⟨W, Cash, Term, M, G, H,
      hW, hCash, hTerm, hTermMeas, hMI, hGI, hHI, hMzero, hGH, hUpper⟩
    let τ : Ω → ℝ≥0 := fun ω =>
      (min (ruinTime X x D ω) (n : ℝ≥0∞)).toNNReal
    have hτmeas : Measurable (fun ω => (τ ω : ℝ)) :=
      avram_wave7_08_actual_truncated_clock_real_measurable_of_source
        X x D n hRuinMeas
    have hCashI' : Integrable (fun ω =>
        (∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iic (τ ω : ℝ),
          ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)).toReal) P :=
      avram_wave6_08_original_bounded_random_clock_full_stieltjes_cash_integrable
        X x C D hD q τ (n : ℝ≥0) hτmeas (hClock n hn).1
    have hCashEq : Cash = (fun ω =>
        (∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iic (τ ω : ℝ),
          ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)).toReal) := by
      funext ω
      exact hCash ω
    have hCashI : Integrable Cash P := by
      rw [hCashEq]
      exact hCashI'
    have hTermI : Integrable Term P :=
      avram_p4_e_localise_original_exact_terminal_L1_from_source_signed_budget
        X x C D hD hxc q τ W hW w hw0 hw_cont hw_neg hw_smooth hw_grad
        Term Cash M G H hTerm hTermMeas hCashI hMI hGI hHI hUpper
    exact ⟨W, Cash, Term, M, G, H, hW, hCash, hTerm,
      hTermI, hCashI, hMI, hGI, hHI, hMzero, hGH, hUpper⟩
  exact avram_sweep16_20261106_natural_l1_residual_to_full_cash
    X q hq w C hC hw0 hw_cont hw_neg hSmooth hw_gen hw_grad
    x hx hxc D hD T hClock hL1
