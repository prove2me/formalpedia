-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave7_05_turn10_original_stopped_C2_hessian_gaussian_halfbracket_integral_expectation_bound
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T09:22:33.545373+00:00
-- url     : https://prove2.me/submissions/eea6ed2d-fd0d-4ddc-b462-147bc760f71f

import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave7_05_turn3_original_allnu_stopped_controlled_gradient_hessian_joint_predictable
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Topology.Order.LeftRightLim

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

/-! Original controlled reserve Hessian Gaussian sigma-square/2 drift expectation envelope. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (w : ℝ → ℝ) (C : ℝ≥0∞)
    (hw : ContDiffOn ℝ 2 w {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (q : ℝ) (T : ℝ≥0)
    (τ : ℕ → Ω → ℝ≥0)
    (hτ : ∀ n, ∀ s : ℝ≥0,
      MeasurableSet[𝓕.rightCont s] {ω : Ω | τ n ω ≤ s})
    (H : ℕ → Ω → ℝ)
    (hHsource : ∀ n, H n = stoppedValue (fun t ω =>
      if t ≤ T then
        (Real.exp (-(q * (t : ℝ))) *
          (let y := Function.leftLim
            (fun s : ℝ≥0 => x + X.X s ω - rightLimit D s ω) t
           if 0 < y ∧ ENNReal.ofReal y < C then iteratedDeriv 2 w y else 0)) *
        (if (t : ℝ≥0∞) ≤ ruinTime X x D ω then (1 : ℝ) else 0)
      else 0) (fun ω => (τ n ω : WithTop ℝ≥0)))
    (K : ℝ) (hK : 0 ≤ K)
    (hHbound : ∀ n ω, |H n ω| ≤ K) :
    ∀ n, Integrable
      (fun ω => (((X.σ : ℝ) ^ 2 / 2) * H n ω)) P ∧
      |∫ ω, (((X.σ : ℝ) ^ 2 / 2) * H n ω) ∂P| ≤
        ((X.σ : ℝ) ^ 2 / 2) * K := by
  classical
  letI : IsProbabilityMeasure P := X.isProbability
  have hc : 0 ≤ ((X.σ : ℝ) ^ 2 / 2) :=
    div_nonneg (sq_nonneg _) (by norm_num)
  intro n
  have hPred :=
    avram_wave7_05_turn3_original_allnu_stopped_controlled_gradient_hessian_joint_predictable
      X x D hD w C hw q T (τ n) (hτ n)
  dsimp only at hPred
  have hMeas : Measurable (H n) := by
    rw [hHsource n]
    exact hPred.2.2.2
  have hDom : ∀ ω : Ω,
      ‖((X.σ : ℝ) ^ 2 / 2) * H n ω‖ ≤
        ((X.σ : ℝ) ^ 2 / 2) * K := by
    intro ω
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg hc]
    exact mul_le_mul_of_nonneg_left (hHbound n ω) hc
  have hInt : Integrable
      (fun ω => (((X.σ : ℝ) ^ 2 / 2) * H n ω)) P :=
    (integrable_const (((X.σ : ℝ) ^ 2 / 2) * K)).mono'
      (measurable_const.mul hMeas).aestronglyMeasurable
      (Filter.Eventually.of_forall hDom)
  have hLower : ∀ ω : Ω,
      -(((X.σ : ℝ) ^ 2 / 2) * K) ≤
        ((X.σ : ℝ) ^ 2 / 2) * H n ω := by
    intro ω
    have hlo := (abs_le.mp (hHbound n ω)).1
    have hz := mul_le_mul_of_nonneg_left hlo hc
    nlinarith
  have hUpper : ∀ ω : Ω,
      ((X.σ : ℝ) ^ 2 / 2) * H n ω ≤
        ((X.σ : ℝ) ^ 2 / 2) * K := by
    intro ω
    have hhi := (abs_le.mp (hHbound n ω)).2
    exact mul_le_mul_of_nonneg_left hhi hc
  have hLowInt :
      -(((X.σ : ℝ) ^ 2 / 2) * K) ≤
        ∫ ω, (((X.σ : ℝ) ^ 2 / 2) * H n ω) ∂P := by
    calc
      -(((X.σ : ℝ) ^ 2 / 2) * K) =
          ∫ _ω : Ω, -(((X.σ : ℝ) ^ 2 / 2) * K) ∂P := by simp
      _ ≤ ∫ ω, (((X.σ : ℝ) ^ 2 / 2) * H n ω) ∂P :=
        integral_mono (integrable_const _) hInt hLower
  have hUpInt :
      (∫ ω, (((X.σ : ℝ) ^ 2 / 2) * H n ω) ∂P) ≤
        ((X.σ : ℝ) ^ 2 / 2) * K := by
    calc
      (∫ ω, (((X.σ : ℝ) ^ 2 / 2) * H n ω) ∂P) ≤
          ∫ _ω : Ω, (((X.σ : ℝ) ^ 2 / 2) * K) ∂P :=
        integral_mono hInt (integrable_const _) hUpper
      _ = ((X.σ : ℝ) ^ 2 / 2) * K := by simp
  exact ⟨hInt, abs_le.mpr ⟨hLowInt, hUpInt⟩⟩
