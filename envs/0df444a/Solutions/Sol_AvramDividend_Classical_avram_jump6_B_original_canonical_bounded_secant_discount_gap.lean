-- Prove2me | solution 1 for AvramDividend.Classical.avram_jump6_B_original_canonical_bounded_secant_discount_gap
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-19T17:20:45.904718+00:00
-- url     : https://prove2.me/submissions/b8aaf30b-1cfe-41a5-b1d1-944b4603091a

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_jump6_B_canonical_stop_dividend_discount_oscillation_bound
import Definitions.Def_AvramDividend_Classical_DividendStrategy
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal BigOperators
noncomputable section

theorem solution
    {Ω : Type*} [MeasurableSpace Ω]
    {𝓕 : Filtration ℝ≥0 ‹MeasurableSpace Ω›}
    (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (ω : Ω) (q : ℝ) (hq : 0 ≤ q)
    (t : ℝ≥0) (j m : ℕ) :
    let Δ : ℝ≥0 := (1 : ℝ≥0) / ((j : ℝ≥0) + 1)
    let v : ℕ → ℝ≥0 := fun i => min ((i : ℝ≥0) * Δ) t
    ∀ (L : ℝ), 0 ≤ L → ∀ (g : ℕ → ℝ),
      (∀ i < m, 0 ≤
        Real.exp (-(q * (v i : ℝ))) -
          Real.exp (-(q * (v (i+1) : ℝ)))) →
      (∀ i < m, g i ≤
        L * (rightLimit D (v (i+1)) ω - rightLimit D (v i) ω)) →
      (∑ i ∈ Finset.range m,
        (Real.exp (-(q * (v i : ℝ))) -
         Real.exp (-(q * (v (i+1) : ℝ)))) * g i) ≤
      L * (q * (Δ : ℝ) *
        (rightLimit D (v m) ω - rightLimit D (v 0) ω)) := by
  intro Δ v L hL g hAlpha hSec
  have hBase :=
    avram_jump6_B_canonical_stop_dividend_discount_oscillation_bound
      D hD ω q hq t j m
  dsimp only at hBase
  calc
    (∑ i ∈ Finset.range m,
      (Real.exp (-(q * (v i : ℝ))) -
       Real.exp (-(q * (v (i+1) : ℝ)))) * g i) ≤
      ∑ i ∈ Finset.range m,
        (Real.exp (-(q * (v i : ℝ))) -
         Real.exp (-(q * (v (i+1) : ℝ)))) *
        (L * (rightLimit D (v (i+1)) ω -
          rightLimit D (v i) ω)) := by
      apply Finset.sum_le_sum
      intro i hi
      exact mul_le_mul_of_nonneg_left
        (hSec i (Finset.mem_range.mp hi))
        (hAlpha i (Finset.mem_range.mp hi))
    _ = L * (∑ i ∈ Finset.range m,
        (Real.exp (-(q * (v i : ℝ))) -
         Real.exp (-(q * (v (i+1) : ℝ)))) *
        (rightLimit D (v (i+1)) ω -
         rightLimit D (v i) ω)) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i hi
      ring
    _ ≤ L * (q * (Δ : ℝ) *
        (rightLimit D (v m) ω - rightLimit D (v 0) ω)) :=
      mul_le_mul_of_nonneg_left hBase hL
