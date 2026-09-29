-- Prove2me | solution 1 for BanditAlgorithm.gittins_finite_reward_le_index_policy_add_terminal
-- status  : ACCEPTED   (prove)
-- author  : @Harry_Xu
-- created : 2026-08-01T17:00:53.922222+00:00
-- url     : https://prove2.me/submissions/57828db2-cda0-4445-8de7-60aab0db7637

import Theorems.Thm_BanditAlgorithm_gittins_finite_prevailing_charge_accounting
import Theorems.Thm_BanditAlgorithm_gittins_finite_prevailing_charge_interleaving

open MeasureTheory ProbabilityTheory ENNReal

theorem solution
    {k : ℕ} {S : Type*} [MeasurableSpace S]
    [StandardBorelSpace S]
    (P : Kernel S S) [IsMarkovKernel P]
    {r : S → ℝ} (hr : Measurable r)
    {α : ℝ} (hα0 : 0 < α) (hα1 : α < 1)
    (hint : BanditAlgorithm.DiscountedRewardIntegrable P r α)
    (π πstar : BanditAlgorithm.MarkovBanditPolicy k S)
    (hπstar : BanditAlgorithm.IsGittinsIndexPolicy P r α πstar)
    (x : Fin k → S) (N : ℕ) :
    (∑ n ∈ Finset.range N,
      α ^ n * BanditAlgorithm.markovBanditRoundReward P r π x n) ≤
      (∑ n ∈ Finset.range N,
        α ^ n * BanditAlgorithm.markovBanditRoundReward P r πstar x n) +
      α ^ N * BanditAlgorithm.markovBanditExpectedRetirementPotential
        P r α πstar x N := by
  have haccounting :=
    BanditAlgorithm.gittins_finite_prevailing_charge_accounting
      P hr hα0 hα1 hint π πstar hπstar x N
  calc
    (∑ n ∈ Finset.range N,
        α ^ n * BanditAlgorithm.markovBanditRoundReward P r π x n) ≤
        BanditAlgorithm.markovBanditFinitePrevailingChargeValue
          P r α π x N := haccounting.1
    _ ≤ BanditAlgorithm.markovBanditFinitePrevailingChargeValue
          P r α πstar x N :=
      BanditAlgorithm.gittins_finite_prevailing_charge_interleaving
        P hr hα0 hα1 hint π πstar hπstar x N
    _ = (∑ n ∈ Finset.range N,
          α ^ n * BanditAlgorithm.markovBanditRoundReward P r πstar x n) +
        α ^ N * BanditAlgorithm.markovBanditExpectedRetirementPotential
          P r α πstar x N := haccounting.2
