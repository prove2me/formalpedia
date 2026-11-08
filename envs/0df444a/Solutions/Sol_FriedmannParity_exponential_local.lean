-- Prove2me | solution 1 for FriedmannParity.exponential_local
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-08T04:01:47.008013+00:00
-- url     : https://prove2.me/submissions/d8bd3fca-0005-4833-a0c1-4661b4d93e29

import Theorems.Thm_FriedmannParity_exponential_binary
import Definitions.Def_friedmann_parity

set_option autoImplicit false


open FriedmannParity in
theorem solution : ExponentialLocal := by
  rcases FriedmannParity.exponential_binary with ⟨C, hC, hExp⟩
  refine ⟨C, hC, fun n hn => ?_⟩
  rcases hExp false n hn with ⟨N, G, ι, _, hedge, hprio, hhard⟩
  exact ⟨N, G, ι, hedge, hprio, hhard⟩
