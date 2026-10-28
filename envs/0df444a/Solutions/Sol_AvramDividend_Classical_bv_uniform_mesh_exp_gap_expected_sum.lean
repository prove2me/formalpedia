-- Prove2me | solution 1 for AvramDividend.Classical.bv_uniform_mesh_exp_gap_expected_sum
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-27T00:44:35.651765+00:00
-- url     : https://prove2.me/submissions/a4654616-2289-4b75-bbcb-3500db1b16f6

import Theorems.Thm_AvramDividend_Classical_bv_actual_drift_deficit_increment_exp_gap_expectation
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Tactic.Ring

open AvramDividend.Classical MeasureTheory Set Finset
open scoped NNReal ENNReal BigOperators
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hBV : X.BoundedVariation)
    (N : ℕ) (ts : ℕ → ℝ≥0) (δ : ℝ≥0)
    (D : ℕ → Ω → ℝ)
    (hD : ∀ k ω, D k ω =
      X.drift * (ts k : ℝ) - X.X (ts k) ω)
    (hOrder : ∀ k : ℕ, k < N → ts k ≤ ts (k + 1))
    (hStep : ∀ k : ℕ, k < N → ts (k + 1) - ts k = δ)
    (θ : ℝ) (hθ : 1 ≤ θ)
    (a : ℝ)
    (hInt : ∀ k : ℕ, k < N →
      Integrable
        (fun ω => (1 : ℝ) -
          Real.exp (-θ * (D (k + 1) ω - D k ω))) P) :
    (∫ ω, 4 * a * ∑ k ∈ Finset.range N,
      (1 - Real.exp (-θ * (D (k + 1) ω - D k ω))) ∂P) =
      4 * a * (N : ℝ) *
        (1 - Real.exp (-((δ : ℝ) *
          ∫ y in Iio (0 : ℝ), (1 - Real.exp (θ * y)) ∂X.ν))) := by
  rw [integral_const_mul, integral_finset_sum _ (fun k hk => hInt k (Finset.mem_range.mp hk))]
  rw [Finset.sum_congr rfl (g := fun _ => 1 - Real.exp (-((δ : ℝ) *
      ∫ y in Iio (0 : ℝ), (1 - Real.exp (θ * y)) ∂X.ν))) ?_]
  · simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]; ring
  · intro k hk
    have hk' := Finset.mem_range.mp hk
    have := AvramDividend.Classical.bv_actual_drift_deficit_increment_exp_gap_expectation X hBV
      (ts k) (ts (k + 1)) (hOrder k hk') θ hθ
    simp only [hD]
    rw [this, hStep k hk']
