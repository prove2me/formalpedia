-- Prove2me | solution 1 for BanditAlgorithm.moss_regret_intermediate_bound
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @MKPynnic
-- created : 2026-07-21T02:31:20.958788+00:00
-- url     : https://prove2.me/submissions/4383b9ba-e264-43a6-abbc-ad4f5af7b133
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_BanditAlgorithm_moss_regret_large_gap_occupation_reduction
import Theorems.Thm_BanditAlgorithm_moss_large_gap_occupation_sum_bound

/-!
Source-faithful reduction of Lattimore and Szepesvari, *Bandit Algorithms*
(CUP 2020), proof of Theorem 9.1, printed pp. 126--127 (PDF pp. 135--136).
The first child is the displayed regret/optimal-deficit split on p. 126; the
second is the displayed Lemma 8.2 large-gap occupation sum continued on p. 127.
-/

open MeasureTheory ProbabilityTheory

open BanditAlgorithm

theorem solution {k : ℕ} (hk : 0 < k)
    {ν : StochasticBandit k} (hν : IsSubgaussianBandit 1 ν)
    {n : ℕ} {π : BanditPolicy k}
    (hπ : IsMOSSPolicy n π) (hkn : k ≤ n) :
    banditRegret ν π n ≤
      24 * Real.sqrt ((k : ℝ) * n) +
        Finset.sum
          (Finset.univ.filter
            (fun i ↦ 8 * Real.sqrt ((k : ℝ) / n) < banditGap ν i))
          (fun i ↦ banditGap ν i + 15 * Real.sqrt ((n : ℝ) / k)) := by
  have hsplit := moss_regret_large_gap_occupation_reduction hk hν hπ hkn
  have hlarge := moss_large_gap_occupation_sum_bound hk hν hπ hkn
  exact hsplit.trans (add_le_add (le_refl _) hlarge)
