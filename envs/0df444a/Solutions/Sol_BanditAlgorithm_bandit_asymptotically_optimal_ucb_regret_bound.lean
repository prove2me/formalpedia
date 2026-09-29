-- Prove2me | solution 1 for BanditAlgorithm.bandit_asymptotically_optimal_ucb_regret_bound
-- status  : ACCEPTED   (prove)
-- author  : @Aphrodite
-- created : 2026-07-22T15:23:10.395881+00:00
-- url     : https://prove2.me/submissions/0742bca2-94d8-4bca-b130-671f9e27af6e

import Theorems.Thm_BanditAlgorithm_bandit_regret_decomposition
import Theorems.Thm_BanditAlgorithm_asymptotic_ucb_suboptimal_arm_expected_pull_count_bound

open MeasureTheory ProbabilityTheory

/-!
Reduction of Lattimore--Szepesvári, *Bandit Algorithms* (CUP 2020),
Theorem 8.1, Eq. (8.1), printed p. 117 / PDF p. 126, using the two
per-suboptimal-arm expectation estimates proved after Eq. (8.4) on printed
pp. 119--120 / PDF pp. 128--129. The proof multiplies those estimates by the
nonnegative gaps and sums them via the regret decomposition (Lemma 4.5,
printed pp. 62--63).
-/
theorem solution {k : ℕ}
    {ν : BanditAlgorithm.StochasticBandit k}
    (hν : BanditAlgorithm.IsSubgaussianBandit 1 ν)
    {π : BanditAlgorithm.BanditPolicy k}
    (hπ : BanditAlgorithm.IsAsymptoticUCBPolicy π) (n : ℕ)
    (ε : Fin k → ℝ)
    (hε : ∀ i, 0 < BanditAlgorithm.banditGap ν i →
      ε i ∈ Set.Ioo 0 (BanditAlgorithm.banditGap ν i)) :
    BanditAlgorithm.banditRegret ν π n ≤
      ∑ i ∈ Finset.univ.filter
          (fun i ↦ 0 < BanditAlgorithm.banditGap ν i),
        BanditAlgorithm.banditGap ν i *
          (1 + 5 / ε i ^ 2 +
            2 * (Real.log (BanditAlgorithm.asymptoticUcbSchedule n) +
                Real.sqrt (Real.pi *
                  Real.log (BanditAlgorithm.asymptoticUcbSchedule n)) + 1) /
              (BanditAlgorithm.banditGap ν i - ε i) ^ 2) := by
  rw [BanditAlgorithm.bandit_regret_decomposition ν hν.1 π n]
  calc
    (∑ i, BanditAlgorithm.banditGap ν i *
        ∫ h, (BanditAlgorithm.armPullCount i h : ℝ) ∂
          BanditAlgorithm.banditMeasure ν π n) ≤
      ∑ i, BanditAlgorithm.banditGap ν i *
        (1 + 5 / ε i ^ 2 +
          2 * (Real.log (BanditAlgorithm.asymptoticUcbSchedule n) +
              Real.sqrt (Real.pi *
                Real.log (BanditAlgorithm.asymptoticUcbSchedule n)) + 1) /
            (BanditAlgorithm.banditGap ν i - ε i) ^ 2) := by
      apply Finset.sum_le_sum
      intro i hi
      have hgap_nonneg : 0 ≤ BanditAlgorithm.banditGap ν i := by
        change 0 ≤ BanditAlgorithm.banditOptimalMean ν -
          BanditAlgorithm.banditArmMean ν i
        exact sub_nonneg.mpr
          (Finite.le_ciSup
            (fun j : Fin k ↦ BanditAlgorithm.banditArmMean ν j) i)
      by_cases hgap : 0 < BanditAlgorithm.banditGap ν i
      · have hchild :=
          BanditAlgorithm.asymptotic_ucb_suboptimal_arm_expected_pull_count_bound
            hν hπ n i (ε i) hgap (hε i hgap).1 (hε i hgap).2
        have hchild' :
            (∫ h, (BanditAlgorithm.armPullCount i h : ℝ) ∂
                BanditAlgorithm.banditMeasure ν π n) ≤
              1 + 5 / ε i ^ 2 +
                2 * (Real.log (BanditAlgorithm.asymptoticUcbSchedule n) +
                    Real.sqrt (Real.pi *
                      Real.log (BanditAlgorithm.asymptoticUcbSchedule n)) + 1) /
                  (BanditAlgorithm.banditGap ν i - ε i) ^ 2 := by
          simpa [div_eq_mul_inv, mul_assoc, mul_comm, mul_left_comm] using hchild
        exact mul_le_mul_of_nonneg_left hchild' hgap_nonneg
      · have hzero : BanditAlgorithm.banditGap ν i = 0 :=
          le_antisymm (le_of_not_gt hgap) hgap_nonneg
        simp [hzero]
    _ = _ := by
      rw [Finset.sum_filter]
      apply Finset.sum_congr rfl
      intro i hi
      by_cases hgap : 0 < BanditAlgorithm.banditGap ν i
      · simp [hgap]
      · have hgap_nonneg : 0 ≤ BanditAlgorithm.banditGap ν i := by
          change 0 ≤ BanditAlgorithm.banditOptimalMean ν -
            BanditAlgorithm.banditArmMean ν i
          exact sub_nonneg.mpr
            (Finite.le_ciSup
              (fun j : Fin k ↦ BanditAlgorithm.banditArmMean ν j) i)
        have hzero : BanditAlgorithm.banditGap ν i = 0 :=
          le_antisymm (le_of_not_gt hgap) hgap_nonneg
        simp [hgap, hzero]
