-- Prove2me | solution 1 for AvramDividend.Classical.bv_survival_mesh_bound_normalized_exponent
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-27T07:39:11.618983+00:00
-- url     : https://prove2.me/submissions/48017e53-a022-4570-a9b2-19bd8500b89d

import Theorems.Thm_AvramDividend_Classical_bv_strict_survival_expected_deficit_uniform_mesh_bound
import Theorems.Thm_AvramDividend_Classical_bv_exponent_negative_jump_deficit_exact
import Mathlib.MeasureTheory.Integral.Bochner.Basic

open AvramDividend.Classical MeasureTheory Set Finset
open scoped NNReal ENNReal BigOperators
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hBV : X.BoundedVariation)
    (T : ℝ≥0) (N : ℕ) (ts : ℕ → ℝ≥0) (δ : ℝ≥0)
    (D : ℕ → Ω → ℝ)
    (hD : ∀ k ω, D k ω =
      X.drift * (ts k : ℝ) - X.X (ts k) ω)
    (hEnd : ∀ ω, D N ω - D 0 ω =
      (T : ℝ) * X.drift - X.X T ω)
    (hOrder : ∀ k : ℕ, k < N → ts k ≤ ts (k + 1))
    (hWithin : ∀ k : ℕ, k < N → ts (k + 1) ≤ T)
    (hStep : ∀ k : ℕ, k < N → ts (k + 1) - ts k = δ)
    (hStepReal : ∀ k : ℕ, k < N →
      (ts (k + 1) : ℝ) - (ts k : ℝ) = (δ : ℝ))
    (a C : ℝ) (ha : 0 < a)
    (haEq : a = X.drift * (δ : ℝ))
    (hPref : 4 * a * (N : ℝ) = C)
    (hθ : 1 ≤ (1 / (2 * a) : ℝ))
    (hLeft : Integrable
      ({ω : Ω | (T : ℝ≥0∞) < barrierRuinTime X 0 ω}.indicator
        (fun ω => D N ω - D 0 ω)) P)
    (hRight : Integrable
      (fun ω => 4 * a * ∑ k ∈ Finset.range N,
        (1 - Real.exp (-((D (k + 1) ω - D k ω) / (2 * a))))) P)
    (hCellInt : ∀ k : ℕ, k < N →
      Integrable
        (fun ω => (1 : ℝ) -
          Real.exp (-(1 / (2 * a)) *
            (D (k + 1) ω - D k ω))) P) :
    (∫ ω, {ω : Ω | (T : ℝ≥0∞) < barrierRuinTime X 0 ω}.indicator
      (fun ω => (T : ℝ) * X.drift - X.X T ω) ω ∂P) ≤
      C * (1 - Real.exp (-((δ : ℝ) *
        (X.drift * (1 / (2 * a)) - X.ψ (1 / (2 * a)))))) := by
  have h := bv_strict_survival_expected_deficit_uniform_mesh_bound X hBV T N ts δ D hD hOrder hWithin
    hStep hStepReal a ha haEq hθ hLeft hRight hCellInt
  have hfun : (fun ω => {ω : Ω | (T : ℝ≥0∞) < barrierRuinTime X 0 ω}.indicator
      (fun ω => (T : ℝ) * X.drift - X.X T ω) ω) =
      (fun ω => {ω : Ω | (T : ℝ≥0∞) < barrierRuinTime X 0 ω}.indicator
      (fun ω => D N ω - D 0 ω) ω) := by
    funext ω; simp only [hEnd]
  rw [hfun, bv_exponent_negative_jump_deficit_exact X hBV _ hθ, ← hPref]
  exact h
