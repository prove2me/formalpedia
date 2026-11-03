-- Prove2me | solution 1 for AvramDividend.Classical.avram_chat07b_original_deterministic_horizon_real_cash_budget_to_ENNReal
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-02T09:32:43.533192+00:00
-- url     : https://prove2.me/submissions/7d5c1a97-6be0-4e8f-80a5-d1dc9d069ce0

import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave6_06_original_bounded_clock_stieltjes_cash_ae_finite
import Theorems.Thm_AvramDividend_Classical_avram_wave5_03_original_real_horizon_full_stieltjes_reward_integrable_L1
import Theorems.Thm_AvramDividend_Classical_avram_wave6_06_original_inclusive_random_clock_real_cash_budget_to_ennreal
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (C : ℝ≥0∞)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (q T B : ℝ) (hT : 0 ≤ T)
    (hRealBudget :
      (∫ ω, (∫⁻ s in paymentTimes (ruinTime X x D ω) ∩ Iic T,
        ENNReal.ofReal (Real.exp (-(q * s))) ∂(dividendMeasure D ω)).toReal ∂P) ≤ B) :
    (∫⁻ ω, ∫⁻ s in paymentTimes (ruinTime X x D ω) ∩ Iic T,
      ENNReal.ofReal (Real.exp (-(q * s))) ∂(dividendMeasure D ω) ∂P) ≤
      ENNReal.ofReal B := by
  let t0 : ℝ≥0 := ⟨T, hT⟩
  let τ : Ω → ℝ≥0 := fun _ => t0
  let Cash : Ω → ℝ := fun ω =>
    (∫⁻ s in paymentTimes (ruinTime X x D ω) ∩ Iic (τ ω : ℝ),
      ENNReal.ofReal (Real.exp (-(q * s))) ∂(dividendMeasure D ω)).toReal
  have hBound : ∀ ω, τ ω ≤ t0 := fun _ => le_rfl
  have hFinite : ∀ᵐ ω ∂P,
      (∫⁻ s in paymentTimes (ruinTime X x D ω) ∩ Iic (τ ω : ℝ),
        ENNReal.ofReal (Real.exp (-(q * s))) ∂(dividendMeasure D ω)) < ⊤ := by
    exact avram_wave6_06_original_bounded_clock_stieltjes_cash_ae_finite
      X x C D hD q τ t0 hBound
  have hCashEq : ∀ ω, Cash ω =
      (∫⁻ s in paymentTimes (ruinTime X x D ω) ∩ Iic (τ ω : ℝ),
        ENNReal.ofReal (Real.exp (-(q * s))) ∂(dividendMeasure D ω)).toReal := by
    intro ω
    rfl
  have hCashI : Integrable Cash P := by
    exact avram_wave5_03_original_real_horizon_full_stieltjes_reward_integrable_L1
      X x C D hD T hT q
  have hReal : (∫ ω, Cash ω ∂P) ≤ B := by
    exact hRealBudget
  have hENN :=
    avram_wave6_06_original_inclusive_random_clock_real_cash_budget_to_ennreal
      X x C D hD q τ Cash hCashEq hFinite hCashI B hReal
  exact hENN
