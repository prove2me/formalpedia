-- Prove2me | solution 1 for AvramDividend.Classical.avram_sweep16_original_localized_ito_no_ui_ruin_cash
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-05T18:38:24.245055+00:00
-- url     : https://prove2.me/submissions/88f3ff8f-c8e9-443f-af32-2d880745b0fb

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_sweep16_original_natural_ruin_cofinal_local_budget_to_cash
import Theorems.Thm_AvramDividend_Classical_avram_sweep16_original_localized_ito_witnesses_budget_each_clock
import Theorems.Thm_AvramDividend_Classical_avram_sweep16_original_double_min_clock_literal_extended_bounds
import Theorems.Thm_AvramDividend_Classical_avram_sweep16_original_double_min_toNNReal_clock_rightcont_stopping
import Theorems.Thm_AvramDividend_Classical_avram_sweep16_original_double_min_clock_nnreal_le_n
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q : ℝ) (hq : 0 < q) (w : ℝ → ℝ)
    (C : ℝ≥0∞) (hC : 0 < C)
    (hw0 : 0 ≤ w 0) (hw_cont : ContinuousOn w (Ici 0))
    (hw_neg : ∀ y : ℝ, y < 0 → w y = 0)
    (hw_smooth : (¬ X.BoundedVariation → ContDiffOn ℝ 2 w {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C}) ∧
      (X.BoundedVariation → ContDiffOn ℝ 1 w {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C}))
    (hw_gen : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C →
      X.GeneratorIntegrable w y ∧ X.generator w y - q * w y ≤ 0)
    (hw_grad : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C → 1 ≤ deriv w y)
    (x : ℝ) (hx : 0 ≤ x) (hxc : ENNReal.ofReal x ≤ C)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (n : ℕ) (S : ℕ → Ω → ℝ≥0∞)
    (hSstop : ∀ k, IsStoppingTime 𝓕.rightCont (S k))
    (hSmono : ∀ ω, Monotone (fun k => S k ω))
    (hSsup : ∀ ω, (⨆ k : ℕ, S k ω) = ⊤)
    (τ : ℕ → Ω → ℝ≥0)
    (hτeq : ∀ k ω, τ k ω = (min (min (ruinTime X x D ω) (n : ℝ≥0∞)) (S k ω)).toNNReal)
    (hResidual : ∀ k : ℕ, ∃ W Cash Term M G H : Ω → ℝ,
      (∀ ω, W ω = if τ k ω = 0 ∨
        (τ k ω : ℝ≥0∞) < ruinTime X x D ω then
        x + X.X (τ k ω) ω - rightLimit D (τ k ω) ω
        else riskProcess X x D (τ k ω) ω) ∧
      (∀ ω, Cash ω =
        (∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iic (τ k ω : ℝ),
          ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)).toReal) ∧
      (∀ ω, Term ω = Real.exp (-(q * (τ k ω : ℝ))) * w (W ω)) ∧
      Integrable Term P ∧ Integrable Cash P ∧
      Integrable M P ∧ Integrable G P ∧ Integrable H P ∧
      (∫ ω, M ω ∂P) = 0 ∧
      (∀ᵐ ω ∂P, G ω + H ω ≤ 0) ∧
      (∀ᵐ ω ∂P, Term ω + Cash ω ≤ w x + M ω + G ω + H ω)) :
    (∫⁻ ω, ∫⁻ t in paymentTimes (ruinTime X x D ω) ∩
      Iic (((min (ruinTime X x D ω) (n : ℝ≥0∞)).toNNReal : ℝ)),
      ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω) ∂P) ≤
    ENNReal.ofReal (w x) := by
  have hBound : ∀ k ω, τ k ω ≤ (n : ℝ≥0) := by
    intro k ω
    rw [hτeq k ω]
    exact avram_sweep16_original_double_min_clock_nnreal_le_n
      X x D n S k ω
  have hStop : ∀ k, IsStoppingTime 𝓕.rightCont
      (fun ω => (τ k ω : WithTop ℝ≥0)) := by
    intro k
    have hPhysical :=
      avram_sweep16_original_double_min_toNNReal_clock_rightcont_stopping
        X x C D hD n S hSstop k
    have hEq :
        (fun ω => (τ k ω : WithTop ℝ≥0)) =
        (fun ω => ((min (min (ruinTime X x D ω) (n : ℝ≥0∞))
          (S k ω)).toNNReal : WithTop ℝ≥0)) := by
      funext ω
      exact congrArg (fun v : ℝ≥0 => (v : WithTop ℝ≥0)) (hτeq k ω)
    rw [hEq]
    exact hPhysical
  have hRuin : ∀ k ω, (τ k ω : ℝ≥0∞) ≤ ruinTime X x D ω := by
    intro k ω
    rw [hτeq k ω]
    exact (avram_sweep16_original_double_min_clock_literal_extended_bounds
      X x D n S k ω).2.1
  have hLocal :=
    avram_sweep16_original_localized_ito_witnesses_budget_each_clock
      X q hq w C hC hw0 hw_cont hw_neg hw_smooth hw_gen hw_grad
      x hx hxc D hD n S τ hτeq hBound hStop hRuin hResidual
  exact avram_sweep16_original_natural_ruin_cofinal_local_budget_to_cash
    X x C D hD q n w S hSstop hSmono hSsup hLocal
