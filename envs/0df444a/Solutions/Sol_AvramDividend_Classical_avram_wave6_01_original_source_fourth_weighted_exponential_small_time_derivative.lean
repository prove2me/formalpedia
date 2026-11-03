-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave6_01_original_source_fourth_weighted_exponential_small_time_derivative
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-02T09:36:35.7193+00:00
-- url     : https://prove2.me/submissions/f3f758d8-5bf0-4335-a909-5dc3d5eebcba

import Mathlib.Analysis.Complex.Exponential
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave6_01_original_finite_exponential_test_small_time_source_derivative
import Theorems.Thm_AvramDividend_Classical_avram_wave6_01_original_source_shifted_fourth_laplace_difference_weighted_jump_moment
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal BigOperators
theorem solution {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ} (X : SpectrallyNegativeLevy P 𝓕)
    (ρ θ : ℝ) (hρ : 0 ≤ ρ) (hθ : 0 ≤ θ) :
    Tendsto
      (fun h : ℝ =>
        (∫ ω, Real.exp (ρ * X.X (Real.toNNReal h) ω) *
          (Real.exp (θ * X.X (Real.toNNReal h) ω) - 1) ^ 4 ∂P) / h)
      (nhdsWithin (0 : ℝ) (Ioi 0))
      (nhds (∫ y in Iio (0 : ℝ), Real.exp (ρ * y) *
        (Real.exp (θ * y) - 1) ^ 4 ∂X.ν)) := by
  classical
  let I : Finset ℕ := Finset.range 5
  let c : ℕ → ℝ := fun i =>
    if i = 0 then 1 else if i = 1 then -4 else if i = 2 then 6 else
    if i = 3 then -4 else 1
  let rate : ℕ → ℝ := fun i => ρ + (i : ℝ) * θ
  have hrates : ∀ i ∈ I, 0 ≤ rate i := by
    intro i hi
    exact add_nonneg hρ (mul_nonneg (Nat.cast_nonneg i) hθ)
  have e1 (z : ℝ) : Real.exp ((ρ + θ) * z) =
      Real.exp (ρ * z) * Real.exp (θ * z) := by rw [add_mul, Real.exp_add]
  have e2 (z : ℝ) : Real.exp ((ρ + 2 * θ) * z) =
      Real.exp (ρ * z) * Real.exp (θ * z) ^ 2 := by
    rw [show (ρ + 2 * θ) * z = ρ * z + (θ * z + θ * z) by ring,
      Real.exp_add, Real.exp_add]; ring
  have e3 (z : ℝ) : Real.exp ((ρ + 3 * θ) * z) =
      Real.exp (ρ * z) * Real.exp (θ * z) ^ 3 := by
    rw [show (ρ + 3 * θ) * z = ρ * z + ((θ * z + θ * z) + θ * z) by ring]
    simp only [Real.exp_add]; ring
  have e4 (z : ℝ) : Real.exp ((ρ + 4 * θ) * z) =
      Real.exp (ρ * z) * Real.exp (θ * z) ^ 4 := by
    rw [show (ρ + 4 * θ) * z = ρ * z + ((θ * z + θ * z) + (θ * z + θ * z)) by ring]
    simp only [Real.exp_add]; ring
  have hpoly (z : ℝ) : (∑ i ∈ I, c i * Real.exp (rate i * z)) =
      Real.exp (ρ * z) * (Real.exp (θ * z) - 1) ^ 4 := by
    simp [I, c, rate, Finset.sum_range_succ, e1, e2, e3, e4]
    ring
  have hc : (∑ i ∈ I, c i) = 0 := by
    norm_num [I, c, Finset.sum_range_succ]
  have hlim : (∑ i ∈ I, c i * laplaceExponent X.c X.σ X.ν (rate i)) =
      ∫ y in Iio (0 : ℝ), Real.exp (ρ * y) *
        (Real.exp (θ * y) - 1) ^ 4 ∂X.ν := by
    have he := avram_wave6_01_original_source_shifted_fourth_laplace_difference_weighted_jump_moment X ρ θ hρ hθ
    change (∑ i ∈ I, c i * X.ψ (rate i)) = _
    simp [I, c, rate, Finset.sum_range_succ]
    convert he using 1 <;> ring
  have hfun : (fun h : ℝ =>
      ((∫ ω, ∑ i ∈ I, c i * Real.exp (rate i * X.X (Real.toNNReal h) ω) ∂P) -
        ∑ i ∈ I, c i) / h) =
      (fun h : ℝ => (∫ ω, Real.exp (ρ * X.X (Real.toNNReal h) ω) *
        (Real.exp (θ * X.X (Real.toNNReal h) ω) - 1) ^ 4 ∂P) / h) := by
    funext h
    have he : (fun ω : Ω => ∑ i ∈ I, c i * Real.exp (rate i * X.X (Real.toNNReal h) ω)) =
        (fun ω : Ω => Real.exp (ρ * X.X (Real.toNNReal h) ω) *
          (Real.exp (θ * X.X (Real.toNNReal h) ω) - 1) ^ 4) :=
      funext (fun ω => hpoly (X.X (Real.toNNReal h) ω))
    rw [hc, sub_zero, he]
  have h := avram_wave6_01_original_finite_exponential_test_small_time_source_derivative X I c rate hrates
  rw [hfun, hlim] at h
  exact h
