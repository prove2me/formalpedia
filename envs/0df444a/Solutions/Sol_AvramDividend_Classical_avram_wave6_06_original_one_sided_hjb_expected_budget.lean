-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave6_06_original_one_sided_hjb_expected_budget
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-01T22:08:03.875965+00:00
-- url     : https://prove2.me/submissions/190d44ea-0ec2-4253-afc6-171236679927

import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Complex.Exponential
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave6_06_original_zero_clock_piecewise_terminal_nonnegative
import Theorems.Thm_AvramDividend_Classical_avram_wave6_06_original_bounded_clock_stieltjes_cash_ae_finite
import Theorems.Thm_AvramDividend_Classical_avram_wave6_06_original_inclusive_random_clock_real_cash_budget_to_ennreal

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical
noncomputable section

/-- A one-sided source Itô–Meyer estimate suffices for the full stopped cash budget. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q : ℝ) (hq : 0 < q)
    (w : ℝ → ℝ) (C : ℝ≥0∞) (hC : 0 < C)
    (hw0 : 0 ≤ w 0) (hw_cont : ContinuousOn w (Ici 0))
    (hw_neg : ∀ y : ℝ, y < 0 → w y = 0)
    (hw_smooth : (¬ X.BoundedVariation → ContDiffOn ℝ 2 w {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C}) ∧
      (X.BoundedVariation → ContDiffOn ℝ 1 w {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C}))
    (hw_gen : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C →
      X.GeneratorIntegrable w y ∧ X.generator w y - q * w y ≤ 0)
    (hw_grad : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C → 1 ≤ deriv w y)
    (x : ℝ) (hx : 0 ≤ x) (hxc : ENNReal.ofReal x ≤ C)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (τ : Ω → ℝ≥0) (T : ℝ≥0)
    (hτBound : ∀ ω, τ ω ≤ T)
    (hτ : IsStoppingTime 𝓕.rightCont (fun ω => (τ ω : WithTop ℝ≥0)))
    (hτruin : ∀ ω, (τ ω : ℝ≥0∞) ≤ ruinTime X x D ω)
    (W Cash Term M G H : Ω → ℝ)
    (hW : ∀ ω, W ω = if τ ω = 0 ∨ (τ ω : ℝ≥0∞) < ruinTime X x D ω
      then x + X.X (τ ω) ω - rightLimit D (τ ω) ω else riskProcess X x D (τ ω) ω)
    (hCash : ∀ ω, Cash ω = (∫⁻ s in paymentTimes (ruinTime X x D ω) ∩ Iic (τ ω : ℝ),
      ENNReal.ofReal (Real.exp (-(q * s))) ∂(dividendMeasure D ω)).toReal)
    (hTerm : ∀ ω, Term ω = Real.exp (-(q * (τ ω : ℝ))) * w (W ω))
    (hTermI : Integrable Term P) (hCashI : Integrable Cash P)
    (hMI : Integrable M P) (hGI : Integrable G P) (hHI : Integrable H P)
    (hMzero : (∫ ω, M ω ∂P) = 0)
    (hGHnonpos : ∀ᵐ ω ∂P, G ω + H ω ≤ 0)
    (hUpper : ∀ᵐ ω ∂P,
      Term ω + Cash ω ≤ w x + M ω + G ω + H ω) :
    Integrable Cash P ∧ (∫ ω, Term ω + Cash ω ∂P) ≤ w x ∧
    (∫ ω, Cash ω ∂P) ≤ w x ∧
    (∫⁻ ω, ∫⁻ s in paymentTimes (ruinTime X x D ω) ∩ Iic (τ ω : ℝ),
      ENNReal.ofReal (Real.exp (-(q * s))) ∂(dividendMeasure D ω) ∂P) ≤ ENNReal.ofReal (w x) := by
  have hTermNonneg := avram_wave6_06_original_zero_clock_piecewise_terminal_nonnegative
    X q w C hC hw0 hw_cont hw_neg hw_smooth hw_grad x hx hxc D hD τ W Term hW hTerm
  have hCashFinite := avram_wave6_06_original_bounded_clock_stieltjes_cash_ae_finite
    X x C D hD q τ T hτBound
  letI : IsProbabilityMeasure P := X.isProbability
  have hConst : Integrable (fun _ : Ω => w x) P := integrable_const _
  have hRight : Integrable (fun ω => w x + M ω + G ω + H ω) P :=
    ((hConst.add hMI).add hGI).add hHI
  have hTop :
      (∫ ω, Term ω + Cash ω ∂P) ≤
        (∫ ω, w x + M ω + G ω + H ω ∂P) :=
    integral_mono_ae (hTermI.add hCashI) hRight hUpper
  have hGmean : (∫ ω, G ω + H ω ∂P) ≤ 0 :=
    integral_nonpos_of_ae hGHnonpos
  have hTermMean : 0 ≤ (∫ ω, Term ω ∂P) :=
    integral_nonneg_of_ae hTermNonneg
  have hRightMean :
      (∫ ω, w x + M ω + G ω + H ω ∂P) =
        w x + (∫ ω, M ω ∂P) + (∫ ω, G ω + H ω ∂P) := by
    simp [integral_add, hMI, hGI, hHI, add_assoc]
  have hBudget : (∫ ω, Term ω + Cash ω ∂P) ≤ w x := by
    calc
      _ ≤ (∫ ω, w x + M ω + G ω + H ω ∂P) := hTop
      _ = w x + (∫ ω, M ω ∂P) + (∫ ω, G ω + H ω ∂P) := hRightMean
      _ ≤ w x := by rw [hMzero]; linarith only [hGmean]
  have hCashBound : (∫ ω, Cash ω ∂P) ≤ w x := by
    rw [integral_add hTermI hCashI] at hBudget
    linarith only [hBudget, hTermMean]
  refine ⟨hCashI, hBudget, hCashBound, ?_⟩
  exact avram_wave6_06_original_inclusive_random_clock_real_cash_budget_to_ennreal
    X x C D hD q τ Cash hCash hCashFinite hCashI (w x) hCashBound
