-- Prove2me | solution 1 for FriedmannParity.exponential_deterministic
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-08T04:04:02.272529+00:00
-- url     : https://prove2.me/submissions/6b399348-0a20-497f-b63b-b66ebb2d5b66

import Theorems.Thm_FriedmannParity_exponential_binary
import Theorems.Thm_FriedmannParity_exponential_payoff
import Theorems.Thm_FriedmannParity_exponential_stochastic
import Definitions.Def_friedmann_payoff

set_option autoImplicit false


open FriedmannParity in
theorem solution :
    ExponentialLocal ∧ ExponentialGlobal ∧ FriedmannDiscounted.Exponential ∧
      FriedmannDiscounted.ExponentialMeanViaReduction ∧ FriedmannStochastic.Exponential := by
  have hloc : FriedmannParity.ExponentialLocal := by
    rcases FriedmannParity.exponential_binary with ⟨C, hC, hExp⟩
    refine ⟨C, hC, fun n hn => ?_⟩
    rcases hExp false n hn with ⟨N, G, ι, _, hedge, hprio, hhard⟩
    exact ⟨N, G, ι, hedge, hprio, hhard⟩
  have hglob : FriedmannParity.ExponentialGlobal := by
    rcases FriedmannParity.exponential_binary with ⟨C, hC, hExp⟩
    refine ⟨C, hC, fun n hn => ?_⟩
    rcases hExp true n hn with ⟨N, G, ι, _, hedge, hprio, hhard⟩
    exact ⟨N, G, ι, hedge, hprio, hhard⟩
  exact ⟨hloc, hglob, FriedmannParity.exponential_payoff.1,
    FriedmannParity.exponential_payoff.2, FriedmannParity.exponential_stochastic⟩
