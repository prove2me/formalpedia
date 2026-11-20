-- Prove2me | solution 1 for AvramDividend.Classical.avram_jump6_B_original_canonical_rightdiscount_cash_from_leftdiscount_bound_v2
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-19T17:31:54.690924+00:00
-- url     : https://prove2.me/submissions/092836c0-1ec7-4a3f-a429-a4a95718ef50

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
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {𝓕 : Filtration ℝ≥0 mΩ}
    (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (ω : Ω) (q : ℝ) (hq : 0 ≤ q)
    (t : ℝ≥0) (j m : ℕ) :
    let Δ : ℝ≥0 := (1 : ℝ≥0) / ((j : ℝ≥0) + 1)
    let v : ℕ → ℝ≥0 := fun i => min ((i : ℝ≥0) * Δ) t
    ∀ (L : ℝ), 0 ≤ L →
      ∀ (cash gap : ℕ → ℝ),
      (∀ i < m, 0 ≤
        Real.exp (-(q * (v i : ℝ))) -
        Real.exp (-(q * (v (i+1) : ℝ)))) →
      (∀ i < m, gap i ≤
        L * (rightLimit D (v (i+1)) ω - rightLimit D (v i) ω)) →
      (Finset.sum (Finset.range m) (fun i : ℕ =>
        cash i - Real.exp (-(q * (v i : ℝ))) * gap i)) ≤ 0 →
      (Finset.sum (Finset.range m) (fun i : ℕ =>
        cash i - Real.exp (-(q * (v (i+1) : ℝ))) * gap i)) ≤
      L * (q * (Δ : ℝ) *
        (rightLimit D (v m) ω - rightLimit D (v 0) ω)) := by
  intro Δ v L hL cash gap hAlpha hSec hLeft
  have hSource :=
    avram_jump6_B_canonical_stop_dividend_discount_oscillation_bound
      D hD ω q hq t j m
  have hBound :
      (∑ i ∈ Finset.range m,
        (Real.exp (-(q * (v i : ℝ))) -
         Real.exp (-(q * (v (i+1) : ℝ)))) * gap i) ≤
      L * (q * (Δ : ℝ) *
        (rightLimit D (v m) ω - rightLimit D (v 0) ω)) := by
    calc
      _ ≤ ∑ i ∈ Finset.range m,
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
        mul_le_mul_of_nonneg_left hSource hL
  have hIdentity :
      (Finset.sum (Finset.range m) (fun i : ℕ =>
        cash i - Real.exp (-(q * (v (i+1) : ℝ))) * gap i)) =
      (Finset.sum (Finset.range m) (fun i : ℕ =>
        cash i - Real.exp (-(q * (v i : ℝ))) * gap i)) +
      (∑ i ∈ Finset.range m,
        (Real.exp (-(q * (v i : ℝ))) -
         Real.exp (-(q * (v (i+1) : ℝ)))) * gap i) := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i hi
    ring
  rw [hIdentity]
  linarith
