-- Prove2me | solution 1 for BanditAlgorithm.bandit_minimax_lower_bound
-- status  : ACCEPTED   (prove)
-- author  : @jianglsbz
-- created : 2026-07-22T15:24:21.42948+00:00
-- url     : https://prove2.me/submissions/23415813-3316-4c4e-80a4-b54d3711ecda

import Theorems.Thm_BanditAlgorithm_bandit_minimax_gaussian_pair_regret_sum_lower_bound
import Mathlib.Tactic.Linarith

open MeasureTheory ProbabilityTheory

/-!
Reduction of Lattimore--Szepesvari, *Bandit Algorithms* (CUP 2020),
Theorem 15.2, printed pp. 199--201 / PDF pp. 208--210.  The imported child is
the source's stronger two-environment regret-sum certificate obtained from
Eq. (15.3), Lemma 15.1, and the Gaussian KL calculation.  The last source step
observes that one of the two environments must carry at least half the sum.
-/
theorem solution {k n : ℕ} (hk : 1 < k) (hn : k - 1 ≤ n)
    (π : BanditAlgorithm.BanditPolicy k) :
    ∃ μvec : Fin k → ℝ, (∀ i, μvec i ∈ Set.Icc (0 : ℝ) 1) ∧
      Real.sqrt (((k : ℝ) - 1) * n) / 27 ≤
        BanditAlgorithm.banditRegret (BanditAlgorithm.gaussianBandit μvec) π n := by
  rcases
      BanditAlgorithm.bandit_minimax_gaussian_pair_regret_sum_lower_bound hk hn π with
    ⟨μ, μ', hμ, hμ', hsum⟩
  by_cases h : Real.sqrt (((k : ℝ) - 1) * n) / 27 ≤
      BanditAlgorithm.banditRegret (BanditAlgorithm.gaussianBandit μ) π n
  · exact ⟨μ, hμ, h⟩
  · refine ⟨μ', hμ', ?_⟩
    linarith
