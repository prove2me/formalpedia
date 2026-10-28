-- Prove2me | solution 2 for AvramDividend.Classical.integral_indicator_capped_deficit_le_exp_partition
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-27T00:39:20.563558+00:00
-- url     : https://prove2.me/submissions/44930ae0-2c84-49f0-9f3d-5bac40ba5bc0

import Theorems.Thm_AvramDividend_Classical_capped_deficit_partition_exponential_sum_bound
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Analysis.Complex.Exponential
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Linarith

open MeasureTheory Set Finset
open scoped NNReal ENNReal BigOperators
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] (P : Measure Ω)
    (E : Set Ω) (D : ℕ → Ω → ℝ) (N : ℕ)
    (a : ℝ) (ha : 0 < a)
    (hNonneg : ∀ᵐ ω ∂P, ∀ k : ℕ, k < N →
      0 ≤ D (k + 1) ω - D k ω)
    (hCap : ∀ ω ∈ E, ∀ k : ℕ, k < N →
      D (k + 1) ω - D k ω ≤ a)
    (hLeft : Integrable
      (E.indicator (fun ω => D N ω - D 0 ω)) P)
    (hRight : Integrable
      (fun ω => 4 * a * ∑ k ∈ Finset.range N,
        (1 - Real.exp (-((D (k + 1) ω - D k ω) / (2 * a))))) P) :
    (∫ ω, E.indicator (fun ω => D N ω - D 0 ω) ω ∂P) ≤
      (∫ ω, 4 * a * ∑ k ∈ Finset.range N,
        (1 - Real.exp (-((D (k + 1) ω - D k ω) / (2 * a)))) ∂P) := by
  apply integral_mono_ae hLeft hRight
  filter_upwards [hNonneg] with ω hω
  by_cases hE : ω ∈ E
  · rw [indicator_of_mem hE]
    exact AvramDividend.Classical.capped_deficit_partition_exponential_sum_bound
      (fun k => D k ω) N a ha hω (hCap ω hE)
  · rw [indicator_of_notMem hE]
    apply mul_nonneg (by positivity)
    apply Finset.sum_nonneg
    intro k hk
    have h0 := hω k (Finset.mem_range.mp hk)
    have : -((D (k + 1) ω - D k ω) / (2 * a)) ≤ 0 := by
      have : 0 ≤ (D (k + 1) ω - D k ω) / (2 * a) := div_nonneg h0 (by positivity)
      linarith
    have := Real.exp_le_one_iff.mpr this
    linarith
