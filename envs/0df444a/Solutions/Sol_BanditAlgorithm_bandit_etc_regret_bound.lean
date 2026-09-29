-- Prove2me | solution 1 for BanditAlgorithm.bandit_etc_regret_bound
-- status  : ACCEPTED   (prove)
-- author  : @jianglsbz
-- created : 2026-07-19T05:18:15.237252+00:00
-- url     : https://prove2.me/submissions/b13e3cec-019b-475b-9036-91e08cbe8299

import Definitions.Def_banditRegret
import Definitions.Def_etcPolicy
import Theorems.Thm_BanditAlgorithm_bandit_regret_decomposition
import Theorems.Thm_BanditAlgorithm_etc_arm_expected_pull_count_bound

open MeasureTheory ProbabilityTheory

open scoped BigOperators

theorem solution {k : ℕ} (hk : 0 < k) {ν : BanditAlgorithm.StochasticBandit k}
    (hν : BanditAlgorithm.IsSubgaussianBandit 1 ν) {m n : ℕ} (hm : 1 ≤ m)
    (hmn : m * k ≤ n) {π : BanditAlgorithm.BanditPolicy k}
    (hπ : BanditAlgorithm.IsETCPolicy hk m π) :
    BanditAlgorithm.banditRegret ν π n ≤
      m * ∑ i, BanditAlgorithm.banditGap ν i +
        (n - m * k : ℝ) *
          ∑ i, BanditAlgorithm.banditGap ν i *
            Real.exp (-(m * (BanditAlgorithm.banditGap ν i) ^ 2) / 4) := by
  rw [BanditAlgorithm.bandit_regret_decomposition ν hν.1 π n]
  calc
    ∑ i, BanditAlgorithm.banditGap ν i *
          ∫ h, (BanditAlgorithm.armPullCount i h : ℝ) ∂
            (BanditAlgorithm.banditMeasure ν π n) ≤
        ∑ i, BanditAlgorithm.banditGap ν i *
          (m + (n - m * k : ℝ) *
            Real.exp (-(m * (BanditAlgorithm.banditGap ν i) ^ 2) / 4)) := by
      apply Finset.sum_le_sum
      intro i hi
      gcongr
      · change 0 ≤ BanditAlgorithm.banditOptimalMean ν - BanditAlgorithm.banditArmMean ν i
        exact sub_nonneg.mpr
          (Finite.le_ciSup (fun j : Fin k ↦ BanditAlgorithm.banditArmMean ν j) i)
      · exact BanditAlgorithm.etc_arm_expected_pull_count_bound hk hν hm hmn hπ i
    _ = _ := by
      calc
        (∑ i, BanditAlgorithm.banditGap ν i *
            (m + (n - m * k : ℝ) *
              Real.exp (-(m * (BanditAlgorithm.banditGap ν i) ^ 2) / 4))) =
            (∑ i, BanditAlgorithm.banditGap ν i * m) +
              ∑ i, BanditAlgorithm.banditGap ν i *
                ((n - m * k : ℝ) *
                  Real.exp (-(m * (BanditAlgorithm.banditGap ν i) ^ 2) / 4)) := by
          rw [← Finset.sum_add_distrib]
          apply Finset.sum_congr rfl
          intro i hi
          ring
        _ = m * ∑ i, BanditAlgorithm.banditGap ν i +
            (n - m * k : ℝ) *
              ∑ i, BanditAlgorithm.banditGap ν i *
                Real.exp (-(m * (BanditAlgorithm.banditGap ν i) ^ 2) / 4) := by
          have hfirst :
              (∑ i, BanditAlgorithm.banditGap ν i * (m : ℝ)) =
                (m : ℝ) * ∑ i, BanditAlgorithm.banditGap ν i := by
            rw [← Finset.sum_mul Finset.univ
              (fun i : Fin k ↦ BanditAlgorithm.banditGap ν i) (m : ℝ)]
            ring
          have hsecond :
              (∑ i, BanditAlgorithm.banditGap ν i *
                ((n - m * k : ℝ) *
                  Real.exp (-(m * (BanditAlgorithm.banditGap ν i) ^ 2) / 4))) =
                (n - m * k : ℝ) *
                  ∑ i, BanditAlgorithm.banditGap ν i *
                    Real.exp (-(m * (BanditAlgorithm.banditGap ν i) ^ 2) / 4) := by
            rw [Finset.mul_sum Finset.univ
              (fun i : Fin k ↦ BanditAlgorithm.banditGap ν i *
                Real.exp (-(m * (BanditAlgorithm.banditGap ν i) ^ 2) / 4))
              (n - m * k : ℝ)]
            apply Finset.sum_congr rfl
            intro i hi
            ring
          rw [hfirst, hsecond]
