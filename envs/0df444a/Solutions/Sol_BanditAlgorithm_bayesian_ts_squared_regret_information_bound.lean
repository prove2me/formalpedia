-- Prove2me | solution 1 for BanditAlgorithm.bayesian_ts_squared_regret_information_bound
-- status  : ACCEPTED   (prove)
-- author  : @Harry_Xu
-- created : 2026-08-01T23:46:25.470985+00:00
-- url     : https://prove2.me/submissions/a23cb737-9a44-43cc-8603-1b3f3019c75e

import Theorems.Thm_BanditAlgorithm_bayesianAdversarialRegret_eq_sum_round_integral
import Theorems.Thm_BanditAlgorithm_bayesian_ts_round_regret_sq_le_mutualInformation_increment
import Theorems.Thm_BanditAlgorithm_bayesian_history_mutualInformation_endpoint_bound

open MeasureTheory ProbabilityTheory
open scoped BigOperators

namespace BanditAlgorithm

theorem _root_.solution {k n : ℕ} [NeZero k]
    (Q : Measure (Fin n → Fin k → ℝ)) [IsProbabilityMeasure Q]
    (hQ : ∀ᵐ X ∂Q, ∀ (t : Fin n) (a : Fin k), X t a ∈ Set.Icc (0 : ℝ) 1)
    {pi : BanditPolicy k} (hpi : IsBayesianTSPolicy Q pi) :
    ∃ delta : Fin n → ℝ,
      bayesianAdversarialRegret Q pi = ∑ t, delta t ∧
      ∑ t, delta t ^ 2 ≤ ((k : ℝ) / 2) * Real.log k := by
  let delta : Fin n → ℝ := fun t ↦
    ∫ p, (p.1 t (bayesianOptimalAction p.1) - p.1 t ((p.2 t).1))
      ∂bayesianAdversarialMeasure Q pi n le_rfl
  refine ⟨delta, bayesianAdversarialRegret_eq_sum_round_integral Q hQ pi, ?_⟩
  let I : ℕ → ℝ := fun m ↦
    bayesianHistoryMutualInformation Q pi (min m n) (Nat.min_le_right m n)
  have htel :
      ∑ t : Fin n,
          (bayesianHistoryMutualInformation Q pi (t.1 + 1) (Nat.succ_le_iff.mpr t.2) -
            bayesianHistoryMutualInformation Q pi t.1 (Nat.le_of_lt t.2)) =
        bayesianHistoryMutualInformation Q pi n le_rfl -
          bayesianHistoryMutualInformation Q pi 0 (Nat.zero_le n) := by
    calc
      ∑ t : Fin n,
          (bayesianHistoryMutualInformation Q pi (t.1 + 1) (Nat.succ_le_iff.mpr t.2) -
            bayesianHistoryMutualInformation Q pi t.1 (Nat.le_of_lt t.2)) =
          ∑ t : Fin n, (I (t.1 + 1) - I t.1) := by
            apply Finset.sum_congr rfl
            intro t _
            simp only [I, Nat.min_eq_left (Nat.succ_le_iff.mpr t.2),
              Nat.min_eq_left (Nat.le_of_lt t.2)]
      _ = ∑ m ∈ Finset.range n, (I (m + 1) - I m) := by
        exact Fin.sum_univ_eq_sum_range (fun m ↦ I (m + 1) - I m) n
      _ = I n - I 0 := Finset.sum_range_sub I n
      _ = bayesianHistoryMutualInformation Q pi n le_rfl -
          bayesianHistoryMutualInformation Q pi 0 (Nat.zero_le n) := by
        simp [I]
  calc
    ∑ t, delta t ^ 2 ≤
        ∑ t : Fin n, ((k : ℝ) / 2) *
          (bayesianHistoryMutualInformation Q pi (t.1 + 1) (Nat.succ_le_iff.mpr t.2) -
            bayesianHistoryMutualInformation Q pi t.1 (Nat.le_of_lt t.2)) := by
      apply Finset.sum_le_sum
      intro t _
      exact bayesian_ts_round_regret_sq_le_mutualInformation_increment Q hQ hpi t
    _ = ((k : ℝ) / 2) *
        (bayesianHistoryMutualInformation Q pi n le_rfl -
          bayesianHistoryMutualInformation Q pi 0 (Nat.zero_le n)) := by
      rw [← Finset.mul_sum, htel]
    _ ≤ ((k : ℝ) / 2) * Real.log k := by
      gcongr
      exact bayesian_history_mutualInformation_endpoint_bound Q pi

end BanditAlgorithm
