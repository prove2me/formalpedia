-- Prove2me | solution 1 for ConvexOptimization.prekopa_leindler
-- status  : ACCEPTED   (prove)
-- author  : @Yifan Hong
-- created : 2026-08-14T16:24:08.732478+00:00
-- url     : https://prove2.me/submissions/8c8d12a3-fbb1-47ec-9631-c4d105879c48

import Mathlib
import Theorems.Thm_ConvexOptimization_prekopa_leindler_one_dimensional
import Theorems.Thm_ConvexOptimization_prekopa_leindler_dimension_step

open scoped RealInnerProductSpace ENNReal
open MeasureTheory

theorem solution {n : ℕ} (l : ℝ) (hl0 : 0 < l) (hl1 : l < 1)
    (f g h : EuclideanSpace ℝ (Fin n) → ℝ≥0∞)
    (hf : Measurable f) (hg : Measurable g) (hh : Measurable h)
    (hple : ∀ x y : EuclideanSpace ℝ (Fin n),
      f x ^ (1 - l) * g y ^ l ≤ h ((1 - l) • x + l • y)) :
    (∫⁻ x, f x) ^ (1 - l) * (∫⁻ x, g x) ^ l ≤ ∫⁻ x, h x := by
  let PL : ℕ → Prop := fun k =>
    ∀ (l : ℝ) (_hl0 : 0 < l) (_hl1 : l < 1)
      (f g h : EuclideanSpace ℝ (Fin k) → ℝ≥0∞),
      Measurable f → Measurable g → Measurable h →
      (∀ x y : EuclideanSpace ℝ (Fin k),
        f x ^ (1 - l) * g y ^ l ≤ h ((1 - l) • x + l • y)) →
      (∫⁻ x, f x) ^ (1 - l) * (∫⁻ x, g x) ^ l ≤ ∫⁻ x, h x

  have h_zero : PL 0 := by
    dsimp [PL]
    intro l₀ _hl₀ _hl₁ f₀ g₀ h₀ hf₀ hg₀ hh₀ hple₀
    simpa [volume_euclideanSpace_eq_dirac] using hple₀ 0 0

  have h_one : PL 1 := by
    dsimp [PL]
    exact ConvexOptimization.prekopa_leindler_one_dimensional

  have h_step : ∀ k : ℕ, PL 1 → PL k → PL (k + 1) := by
    intro k h₁ hk
    dsimp [PL] at h₁ hk ⊢
    exact ConvexOptimization.prekopa_leindler_dimension_step h₁ hk

  have h_all : ∀ k : ℕ, PL k := by
    intro k
    induction k with
    | zero => exact h_zero
    | succ k hk => exact h_step k h_one hk

  exact h_all n l hl0 hl1 f g h hf hg hh hple
