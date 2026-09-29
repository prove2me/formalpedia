-- Prove2me | solution 1 for BanditAlgorithm.gittins_index_policy_dominates
-- status  : ACCEPTED   (prove)
-- author  : @Harry_Xu
-- created : 2026-07-31T03:05:41.744264+00:00
-- url     : https://prove2.me/submissions/de31e3ff-c2fb-4360-9b81-d0d6d8b8c013

import Theorems.Thm_BanditAlgorithm_gittins_epsilon_optimal_stopping
import Theorems.Thm_BanditAlgorithm_gittins_policy_dominates_of_epsilon_stopping_calibration

open MeasureTheory ProbabilityTheory ENNReal
open BanditAlgorithm

theorem solution
    {k : ℕ} {S : Type*} [MeasurableSpace S]
    [StandardBorelSpace S] (P : Kernel S S) [IsMarkovKernel P]
    {r : S → ℝ} (hr : Measurable r) {α : ℝ} (hα0 : 0 < α) (hα1 : α < 1)
    (hint : DiscountedRewardIntegrable P r α)
    (πstar : MarkovBanditPolicy k S) (hπ : IsGittinsIndexPolicy P r α πstar)
    (x : Fin k → S) :
    ∀ π : MarkovBanditPolicy k S,
      markovBanditDiscountedValue P r α π x ≤
        markovBanditDiscountedValue P r α πstar x := by
  exact gittins_policy_dominates_of_epsilon_stopping_calibration
    P hr hα0 hα1 hint
    (fun y ε hε ↦
      gittins_epsilon_optimal_stopping P hr hα0 hα1 hint y hε)
    πstar hπ x
