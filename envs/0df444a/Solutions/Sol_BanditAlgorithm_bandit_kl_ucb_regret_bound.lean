-- Prove2me | solution 1 for BanditAlgorithm.bandit_kl_ucb_regret_bound
-- status  : ACCEPTED   (prove)
-- author  : @Harry_Xu
-- created : 2026-07-29T02:04:05.106481+00:00
-- url     : https://prove2.me/submissions/c92fc621-1983-4b3d-a8c4-c7ce350f3508

import Theorems.Thm_BanditAlgorithm_bandit_kl_ucb_finite_regret_bound
import Theorems.Thm_BanditAlgorithm_bandit_kl_ucb_asymptotic_regret_bound

open MeasureTheory ProbabilityTheory Filter

/-!
Lattimore--Szepesvári, *Bandit Algorithms*, Theorem 10.6, printed
pp. 137--140.  The theorem has two claims: the finite-horizon estimate proved
on pp. 139--140 using Lemmas 10.7 and 10.8, and the asymptotic limsup estimate
assigned as Exercise 10.2.
-/

theorem solution {k : ℕ} (μvec : Fin k → ℝ)
    (hμ : ∀ i, μvec i ∈ Set.Icc (0 : ℝ) 1)
    (ν : BanditAlgorithm.StochasticBandit k)
    (hν : ν = BanditAlgorithm.bernoulliBandit μvec hμ)
    (π : BanditAlgorithm.BanditPolicy k)
    (hπ : BanditAlgorithm.IsKLUCBPolicy π) :
    (∀ n : ℕ, ∀ ε₁ ε₂ : Fin k → ℝ,
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
              1 / (2 * ε₁ i ^ 2) + 2 / ε₂ i ^ 2)) ∧
    atTop.limsup
        (fun n : ℕ ↦ ENNReal.ofReal
          (BanditAlgorithm.banditRegret ν π n / Real.log n)) ≤
      ∑ i ∈ Finset.univ.filter
          (fun i ↦ 0 < BanditAlgorithm.banditGap ν i),
        ENNReal.ofReal (BanditAlgorithm.banditGap ν i) /
          ENNReal.ofReal
            (BanditAlgorithm.bernoulliRelativeEntropy
              (BanditAlgorithm.banditArmMean ν i)
              (BanditAlgorithm.banditOptimalMean ν)) := by
  exact ⟨
    BanditAlgorithm.bandit_kl_ucb_finite_regret_bound
      μvec hμ ν hν π hπ,
    BanditAlgorithm.bandit_kl_ucb_asymptotic_regret_bound
      μvec hμ ν hν π hπ⟩
