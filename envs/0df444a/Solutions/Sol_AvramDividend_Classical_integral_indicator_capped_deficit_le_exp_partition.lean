-- Prove2me | solution 1 for AvramDividend.Classical.integral_indicator_capped_deficit_le_exp_partition
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-27T00:39:18.435187+00:00
-- url     : https://prove2.me/submissions/fbb23fcc-5377-48bd-91ea-c7723850abf6

import Theorems.Thm_AvramDividend_Classical_capped_deficit_partition_exponential_sum_bound
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Analysis.Complex.Exponential
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Linarith

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Finset
open scoped NNReal ENNReal BigOperators

/-- Integrate the exponential mesh bound over paths satisfying a one-cell cap. -/
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
  · simpa only [Set.indicator_of_mem hE] using
      (AvramDividend.Classical.capped_deficit_partition_exponential_sum_bound
        (fun k => D k ω) N a ha
        (fun k hk => hω k hk)
        (fun k hk => hCap ω hE k hk))
  · rw [Set.indicator_of_notMem hE]
    have hSum : 0 ≤
        ∑ k ∈ Finset.range N,
          (1 - Real.exp (-((D (k + 1) ω - D k ω) / (2 * a)))) := by
      apply Finset.sum_nonneg
      intro k hk
      have hD := hω k (Finset.mem_range.mp hk)
      have hFrac : 0 ≤ (D (k + 1) ω - D k ω) / (2 * a) :=
        div_nonneg hD (by positivity)
      have hExp : Real.exp (-((D (k + 1) ω - D k ω) / (2 * a))) ≤ 1 :=
        Real.exp_le_one_iff.mpr (by linarith)
      exact sub_nonneg.mpr hExp
    exact mul_nonneg (mul_nonneg (by norm_num) ha.le) hSum
