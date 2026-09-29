-- Prove2me | solution 1 for BanditAlgorithm.bandit_kl_ucb_finite_regret_bound
-- status  : ACCEPTED   (prove)
-- author  : @Harry_Xu
-- created : 2026-07-29T02:18:04.193077+00:00
-- url     : https://prove2.me/submissions/9156fd2d-a3d7-4aa2-9c68-41d768c65473

import Theorems.Thm_BanditAlgorithm_bandit_regret_decomposition
import Theorems.Thm_BanditAlgorithm_bandit_kl_ucb_suboptimal_arm_pull_bound

open MeasureTheory ProbabilityTheory Filter

/-!
Lattimore--Szepesvári, *Bandit Algorithms*, Theorem 10.6, printed
pp. 139--140.  The probabilistic content is the imported per-arm pull-count
estimate.  This file performs the standard regret-decomposition bridge.
-/

theorem solution
    {k : ℕ} (μvec : Fin k → ℝ)
    (hμ : ∀ i, μvec i ∈ Set.Icc (0 : ℝ) 1)
    (ν : BanditAlgorithm.StochasticBandit k)
    (hν : ν = BanditAlgorithm.bernoulliBandit μvec hμ)
    (π : BanditAlgorithm.BanditPolicy k)
    (hπ : BanditAlgorithm.IsKLUCBPolicy π) :
    ∀ n : ℕ, ∀ ε₁ ε₂ : Fin k → ℝ,
      (∀ i, 0 < BanditAlgorithm.banditGap ν i →
        0 < ε₁ i ∧ 0 < ε₂ i ∧
          ε₁ i + ε₂ i < BanditAlgorithm.banditGap ν i) →
      BanditAlgorithm.banditRegret ν π n ≤
        ∑ i ∈ Finset.univ.filter
            (fun i ↦ 0 < BanditAlgorithm.banditGap ν i),
          BanditAlgorithm.banditGap ν i *
            (Real.log (BanditAlgorithm.klucbExploration n) /
                BanditAlgorithm.bernoulliRelativeEntropy
                  (BanditAlgorithm.banditArmMean ν i + ε₁ i)
                  (BanditAlgorithm.banditOptimalMean ν - ε₂ i) +
              1 / (2 * ε₁ i ^ 2) + 2 / ε₂ i ^ 2) := by
  intro n ε₁ ε₂ hε
  have hInt : ∀ i, Integrable id (ν.P i) := by
    intro i
    rw [hν, BanditAlgorithm.bernoulliBandit]
    exact
      ((integrable_dirac (by finiteness) :
          Integrable id (Measure.dirac (1 : ℝ))).smul_measure
            ENNReal.ofReal_ne_top).add_measure
        ((integrable_dirac (by finiteness) :
          Integrable id (Measure.dirac (0 : ℝ))).smul_measure
            ENNReal.ofReal_ne_top)
  rw [BanditAlgorithm.bandit_regret_decomposition ν hInt π n]
  rw [Finset.sum_filter]
  apply Finset.sum_le_sum
  intro i _
  by_cases hi : 0 < BanditAlgorithm.banditGap ν i
  · rw [if_pos hi]
    exact mul_le_mul_of_nonneg_left
      (BanditAlgorithm.bandit_kl_ucb_suboptimal_arm_pull_bound
        μvec hμ ν hν π hπ n i (ε₁ i) (ε₂ i) hi
          (hε i hi).1 (hε i hi).2.1 (hε i hi).2.2)
      (le_of_lt hi)
  · rw [if_neg hi]
    have hgap_nonneg : 0 ≤ BanditAlgorithm.banditGap ν i := by
      rw [BanditAlgorithm.banditGap]
      exact sub_nonneg.mpr
        (le_ciSup (Finite.bddAbove_range (fun j ↦
          BanditAlgorithm.banditArmMean ν j)) i)
    have hgap_zero : BanditAlgorithm.banditGap ν i = 0 :=
      le_antisymm (le_of_not_gt hi) hgap_nonneg
    simp [hgap_zero]
