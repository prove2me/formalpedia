-- Prove2me | solution 1 for BanditAlgorithm.bandit_ucb_regret_bound
-- status  : ACCEPTED   (prove)
-- author  : @Hartmann_Psi
-- created : 2026-07-18T15:50:25.966415+00:00
-- url     : https://prove2.me/submissions/d1fa3afa-5968-4a87-af13-047ba39bc5d6

import Theorems.Thm_BanditAlgorithm_bandit_regret_decomposition
import Theorems.Thm_BanditAlgorithm_ucb_suboptimal_arm_expected_pull_count
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Data.Fintype.Order

/-!
Source-faithful reduction of Lattimore--Szepesvari, *Bandit Algorithms*,
Theorem 7.1 (printed pp. 105--108; online PDF pp. 113--116).  The book first
uses the reusable regret decomposition Lemma 4.5 / Eq. (4.5) (printed p. 62;
online PDF p. 70), then proves the per-suboptimal-arm estimate
`E[T_i(n)] <= 3 + 16 log(n) / Delta_i^2` at the end of the proof (printed
p. 108; online PDF p. 116).  The formal bridge below performs the remaining
finite-sum arithmetic, including the zero-gap arms.
-/

open MeasureTheory ProbabilityTheory
open BanditAlgorithm

theorem solution {k : ℕ} (hk : 0 < k) {nu : StochasticBandit k}
    (hnu : IsSubgaussianBandit 1 nu) {n : ℕ} (hn : 0 < n)
    {pi : BanditPolicy k} (hpi : IsUCBPolicy (1 / (n : ℝ) ^ 2) pi) :
    banditRegret nu pi n ≤
      3 * ∑ i, banditGap nu i +
        ∑ i ∈ Finset.univ.filter (fun i ↦ 0 < banditGap nu i),
          16 * Real.log n / banditGap nu i := by
  rw [bandit_regret_decomposition nu hnu.1]
  calc
    ∑ i, banditGap nu i *
          ∫ h, (armPullCount i h : ℝ) ∂( banditMeasure nu pi n) ≤
        ∑ i, (3 * banditGap nu i +
          if 0 < banditGap nu i then 16 * Real.log n / banditGap nu i else 0) := by
      apply Finset.sum_le_sum
      intro i hi
      by_cases hgap : 0 < banditGap nu i
      · have hpull := ucb_suboptimal_arm_expected_pull_count hk hnu hn hpi i hgap
        rw [if_pos hgap]
        have hgap0 : banditGap nu i ≠ 0 := ne_of_gt hgap
        calc
          banditGap nu i * ∫ h, (armPullCount i h : ℝ) ∂( banditMeasure nu pi n) ≤
              banditGap nu i *
                (3 + 16 * Real.log n / (banditGap nu i) ^ 2) := by
                  exact mul_le_mul_of_nonneg_left hpull hgap.le
          _ = 3 * banditGap nu i + 16 * Real.log n / banditGap nu i := by
                field_simp
      · have hgap0 : banditGap nu i = 0 := by
          apply le_antisymm
          · exact le_of_not_gt hgap
          · rw [banditGap, sub_nonneg]
            exact Finite.le_ciSup (fun j : Fin k ↦ banditArmMean nu j) i
        simp [hgap0]
    _ = 3 * ∑ i, banditGap nu i +
          ∑ i ∈ Finset.univ.filter (fun i ↦ 0 < banditGap nu i),
            16 * Real.log n / banditGap nu i := by
      rw [Finset.sum_add_distrib, Finset.mul_sum]
      congr 1
      rw [Finset.sum_filter]
