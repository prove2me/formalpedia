-- Prove2me | solution 1 for BanditAlgorithm.moss_large_gap_occupation_sum_bound
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @MKPynnic
-- created : 2026-07-21T02:38:37.76566+00:00
-- url     : https://prove2.me/submissions/44b0e9b9-7ef9-4273-a713-497467c93352
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_BanditAlgorithm_moss_large_gap_arm_expected_pull_bound

/-!
Source-faithful finite-sum reduction of Lattimore and Szepesvari,
*Bandit Algorithms* (CUP 2020), proof of Theorem 9.1, printed pp. 126--127
(PDF pp. 135--136).  The imported theorem is the source's fixed-arm
`kappa_i`/Lemma 8.2 estimate; this file merely sums it over the displayed
large-gap set.
-/

open MeasureTheory ProbabilityTheory

open BanditAlgorithm

theorem solution {k : ℕ} (hk : 0 < k)
    {ν : StochasticBandit k} (hν : IsSubgaussianBandit 1 ν)
    {n : ℕ} {π : BanditPolicy k}
    (hπ : IsMOSSPolicy n π) (hkn : k ≤ n) :
    Finset.sum
        (Finset.univ.filter
          (fun i ↦ 8 * Real.sqrt ((k : ℝ) / n) < banditGap ν i))
        (fun i ↦ banditGap ν i *
          ∫ h, (armPullCount i h : ℝ) ∂(banditMeasure ν π n)) ≤
      Finset.sum
        (Finset.univ.filter
          (fun i ↦ 8 * Real.sqrt ((k : ℝ) / n) < banditGap ν i))
        (fun i ↦ banditGap ν i + 15 * Real.sqrt ((n : ℝ) / k)) := by
  classical
  apply Finset.sum_le_sum
  intro i hi
  exact moss_large_gap_arm_expected_pull_bound hk hν hπ hkn i
    (by simpa using (Finset.mem_filter.mp hi).2)
