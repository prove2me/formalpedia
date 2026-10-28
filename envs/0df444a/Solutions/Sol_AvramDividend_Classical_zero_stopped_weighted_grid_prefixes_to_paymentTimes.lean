-- Prove2me | solution 1 for AvramDividend.Classical.zero_stopped_weighted_grid_prefixes_to_paymentTimes
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-26T18:37:43.558512+00:00
-- url     : https://prove2.me/submissions/cbe4f5f6-3f82-438d-b7ee-9e338fe7bb88

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

/-- Equality on cofinal surviving prefixes extends to the exact stopped reward. -/
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
  have hs : paymentTimes σ = {(0 : ℝ)} ∪ ⋃ n, s n := by
    simpa [s] using paymentTimes_eq_zero_union_filtered_Ioc_of_grid σ grid hcofinal
  have hp (n : ℕ) :
      (∫⁻ t in s n, f t ∂μ) = (∫⁻ t in s n, f t ∂ν) := by
    by_cases hn : (grid n : ℝ≥0∞) < σ
    · simpa [s, Ioc, hn, and_assoc] using hprefix n hn
    · have he : s n = ∅ := by
        ext t
        simp [s, hn]
      simp [he]
  have hd : Directed (fun (a b : Set ℝ) => a ⊆ b) s := by
    simpa [s] using filtered_surviving_Ioc_prefixes_directed σ grid
  have hUnion := directed_stieltjes_prefixes_determine_union_reward μ ν f s hd hp
  rw [hs]
  calc
    (∫⁻ t in ({(0 : ℝ)} ∪ ⋃ n, s n), f t ∂μ) =
        (∫⁻ t in ⋃ n, s n, f t ∂μ) :=
      zero_atom_free_stieltjes_reward_union μ f (⋃ n, s n) hzeroμ
    _ = (∫⁻ t in ⋃ n, s n, f t ∂ν) := hUnion
    _ = (∫⁻ t in ({(0 : ℝ)} ∪ ⋃ n, s n), f t ∂ν) :=
      (zero_atom_free_stieltjes_reward_union ν f (⋃ n, s n) hzeroν).symm
