-- Prove2me | solution 2 for AvramDividend.Classical.zero_stopped_weighted_grid_prefixes_to_paymentTimes
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-26T18:39:07.649557+00:00
-- url     : https://prove2.me/submissions/2877cf5c-7ccc-4607-883f-fa1bc8bd3cd8

import Theorems.Thm_AvramDividend_Classical_paymentTimes_eq_zero_union_filtered_Ioc_of_grid
import Theorems.Thm_AvramDividend_Classical_directed_stieltjes_prefixes_determine_union_reward
import Theorems.Thm_AvramDividend_Classical_filtered_surviving_Ioc_prefixes_directed
import Theorems.Thm_AvramDividend_Classical_zero_atom_free_stieltjes_reward_union
import Mathlib.MeasureTheory.Integral.Lebesgue.Basic

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

theorem solution
    (σ : ℝ≥0∞) (grid : ℕ → ℝ≥0)
    (μ ν : Measure ℝ) (f : ℝ → ℝ≥0∞)
    (hcofinal : ∀ t : ℝ, 0 < t → ENNReal.ofReal t < σ →
      ∃ n : ℕ, t ≤ (grid n : ℝ) ∧ (grid n : ℝ≥0∞) < σ)
    (hprefix : ∀ n : ℕ, (grid n : ℝ≥0∞) < σ →
      (∫⁻ t in Ioc (0 : ℝ) (grid n : ℝ), f t ∂μ) =
        (∫⁻ t in Ioc (0 : ℝ) (grid n : ℝ), f t ∂ν))
    (hzeroμ : μ {(0 : ℝ)} = 0) (hzeroν : ν {(0 : ℝ)} = 0) :
    (∫⁻ t in paymentTimes σ, f t ∂μ) =
      (∫⁻ t in paymentTimes σ, f t ∂ν) := by
  let s : ℕ → Set ℝ := fun n =>
    {t : ℝ | 0 < t ∧ t ≤ (grid n : ℝ) ∧ (grid n : ℝ≥0∞) < σ}
  have hEach (n : ℕ) :
      (∫⁻ t in s n, f t ∂μ) = (∫⁻ t in s n, f t ∂ν) := by
    by_cases hn : (grid n : ℝ≥0∞) < σ
    · have hs : s n = Ioc (0 : ℝ) (grid n : ℝ) := by
        ext t
        simp [s, hn, Set.mem_Ioc]
      rw [hs]
      exact hprefix n hn
    · have hs : s n = ∅ := by
        ext t
        simp [s, hn]
      simp [hs]
  have hDirected : Directed (fun a b : Set ℝ => a ⊆ b) s :=
    filtered_surviving_Ioc_prefixes_directed σ grid
  have hUnion :
      (∫⁻ t in ⋃ n, s n, f t ∂μ) =
      (∫⁻ t in ⋃ n, s n, f t ∂ν) :=
    directed_stieltjes_prefixes_determine_union_reward μ ν f s
      hDirected hEach
  have hPay : paymentTimes σ = {(0 : ℝ)} ∪ ⋃ n, s n := by
    simpa only [s] using
      paymentTimes_eq_zero_union_filtered_Ioc_of_grid σ grid hcofinal
  rw [hPay, zero_atom_free_stieltjes_reward_union μ f
    (⋃ n, s n) hzeroμ,
    zero_atom_free_stieltjes_reward_union ν f
    (⋃ n, s n) hzeroν]
  exact hUnion
