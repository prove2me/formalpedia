-- Prove2me | solution 1 for AvramDividend.Classical.avram_gbB147_original_real_time_H_fixed_t_exponential_bound
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-12T11:27:40.737624+00:00
-- url     : https://prove2.me/submissions/6b792aae-966e-4959-b7b5-e35e23b29e4a

import Mathlib.Probability.Process.Filtration
import Theorems.Thm_AvramDividend_Classical_avram_gbB126_original_physical_postpayment_gradient_uniform_bound
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q : ℝ) (hq : 0 < q) (w : ℝ → ℝ)
    (C : ℝ≥0∞) (hC : 0 < C) (hFiniteCap : C ≠ ⊤)
    (hw_smooth : ContDiffOn ℝ 2 w {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (ρ : Ω → ℝ≥0) (δ : ℝ) (hδ : 0 < δ) (j : ℕ) :
    let H : ℝ → Ω → ℝ := fun t ω =>
      let s : ℝ≥0 := Real.toNNReal t
      let a : ℝ := δ / 2
      let b : ℝ := C.toReal *
        (((j + 1 : ℕ) : ℝ) / ((j + 2 : ℕ) : ℝ))
      let Y : ℝ := x + X.X s ω - rightLimit D s ω
      if s < ρ ω then Real.exp (-(q * t)) *
        (if Y ∈ Icc a b then deriv w Y else 1)
      else 0
    ∃ B : ℝ, 0 ≤ B ∧ ∀ t ω, |H t ω| ≤
        Real.exp (-(q * (t - (Real.toNNReal t : ℝ)))) * B := by
  intro H
  rcases avram_gbB126_original_physical_postpayment_gradient_uniform_bound
    X q hq w C hC hFiniteCap hw_smooth x D ρ δ hδ j
    with ⟨B, hB, hb⟩
  refine ⟨B, hB, ?_⟩
  intro t ω
  let s : ℝ≥0 := Real.toNNReal t
  let a : ℝ := δ / 2
  let b : ℝ := C.toReal * (((j + 1 : ℕ) : ℝ) / ((j + 2 : ℕ) : ℝ))
  let Y : ℝ := x + X.X s ω - rightLimit D s ω
  have h0 : |if s < ρ ω then Real.exp (-(q * (s : ℝ))) *
      (if Y ∈ Icc a b then deriv w Y else 1) else 0| ≤ B := by
    simpa only [s, a, b, Y] using hb s ω
  have heq : H t ω = Real.exp (-(q * (t - (s : ℝ)))) *
      (if s < ρ ω then Real.exp (-(q * (s : ℝ))) *
        (if Y ∈ Icc a b then deriv w Y else 1) else 0) := by
    change (if s < ρ ω then Real.exp (-(q * t)) *
      (if Y ∈ Icc a b then deriv w Y else 1) else 0) =
      Real.exp (-(q * (t - (s : ℝ)))) *
      (if s < ρ ω then Real.exp (-(q * (s : ℝ))) *
        (if Y ∈ Icc a b then deriv w Y else 1) else 0)
    by_cases hs : s < ρ ω
    · simp only [if_pos hs]
      rw [← mul_assoc, ← Real.exp_add]
      congr 1
      ring
    · simp only [if_neg hs, mul_zero]
  rw [heq, abs_mul, Real.abs_exp]
  exact mul_le_mul_of_nonneg_left h0 (le_of_lt (Real.exp_pos _))
