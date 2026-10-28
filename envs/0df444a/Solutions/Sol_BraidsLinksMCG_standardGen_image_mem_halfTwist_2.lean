-- Prove2me | solution 2 for BraidsLinksMCG.standardGen_image_mem_halfTwist
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-28T08:54:56.474878+00:00
-- url     : https://prove2.me/submissions/2c8e9b81-0e7a-4aa3-812b-d6fbeabf17a9

import Mathlib
import Definitions.Def_BraidsLinksMCG_ConfigSpace
import Definitions.Def_BraidsLinksMCG_StandardLoops
import Definitions.Def_TarchaBraids_HalfTwist
import Theorems.Thm_TarchaBraids_pureBraid_le_halfTwist_closure

open BraidsLinksMCG TarchaBraids

theorem solution (n : ℕ) (j : Fin n) :
    (FundamentalGroup.map (configProj (n + 1)) (baseOrdered (n + 1)))
        ((FundamentalGroup.mapOfEq (configIncl n) (configIncl_base n)) (standardGen n j))
      ∈ Subgroup.closure
          (Set.range (fun i : Fin (n + 1 - 1) => halfTwistBraid (n + 1) i)) :=
  TarchaBraids.pureBraid_le_halfTwist_closure (n + 1) ⟨_, rfl⟩
