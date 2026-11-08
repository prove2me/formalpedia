-- Prove2me | solution 1 for FlowAllocationGames.UnitRanking.eq_8_flow_eq_sum_utility
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-07T14:25:56.580052+00:00
-- url     : https://prove2.me/submissions/35930bc1-7813-4873-9c4c-9204ddc2c5d3

import Mathlib
import Definitions.Def_FlowAllocationGames_UnitRanking_Game
import Definitions.Def_FlowAllocationGames_UnitRanking_Profile
import Definitions.Def_FlowAllocationGames_UnitRanking_utility
import Definitions.Def_FlowAllocationGames_UnitRanking_totalFlow

open FlowAllocationGames.UnitRanking in
theorem solution {n m : ℕ} (Γ : Game n m) (a : Profile m) :
    totalFlow Γ a = ∑ v, utility Γ a v := by
  unfold totalFlow utility outFlow
  exact (Finset.sum_fiberwise Finset.univ Γ.tail (clearing Γ a)).symm
