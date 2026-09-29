-- Prove2me | solution 1 for BraidsLinksMCG.standardGen_membership_of_classical_word_v1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-09-23T05:25:18.904917+00:00
-- url     : https://prove2.me/submissions/3cc3dbe8-391e-4508-9530-17d1078e787f

import Mathlib
import Definitions.Def_BraidsLinksMCG_ConfigSpace
import Definitions.Def_BraidsLinksMCG_StandardLoops
import Definitions.Def_TarchaBraids_HalfTwist
import Definitions.Def_TarchaBraids_generation_word_data_v1
import Definitions.Def_TarchaBraids_standard_pure_braid_word_v1

open TarchaBraids
open BraidsLinksMCG

/-- The projected standard generator is the value of the free-group lift on the explicit
half-twist word, so the membership statement follows from the assumed identification and
the fact that the range of a free-group lift is the closure of the range of its values. -/
theorem solution (n : ℕ) (j : Fin n)
    (hclassical :
      (FundamentalGroup.map (configProj (n + 1)) (baseOrdered (n + 1)))
          ((FundamentalGroup.mapOfEq (configIncl n) (BraidsLinksMCG.configIncl_base n))
            (standardGen n j))
        =
      FreeGroup.lift
          (fun i : Fin (n + 1 - 1) => halfTwistBraid (n + 1) i)
          (braidWordFree (standardPureBraidWord n j))) :
    (FundamentalGroup.map (configProj (n + 1)) (baseOrdered (n + 1)))
        ((FundamentalGroup.mapOfEq (configIncl n) (BraidsLinksMCG.configIncl_base n))
          (standardGen n j))
      ∈ Subgroup.closure
          (Set.range (fun i : Fin (n + 1 - 1) => halfTwistBraid (n + 1) i)) := by
  rw [hclassical]
  rw [← FreeGroup.range_lift_eq_closure
    (f := fun i : Fin (n + 1 - 1) => halfTwistBraid (n + 1) i)]
  exact ⟨_, rfl⟩
