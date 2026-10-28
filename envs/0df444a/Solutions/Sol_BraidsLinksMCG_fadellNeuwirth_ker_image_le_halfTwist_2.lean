-- Prove2me | solution 2 for BraidsLinksMCG.fadellNeuwirth_ker_image_le_halfTwist
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-28T08:55:07.427983+00:00
-- url     : https://prove2.me/submissions/3a1713a4-6125-494f-b2fb-13ccd156e7ea

import Mathlib
import Definitions.Def_BraidsLinksMCG_ConfigSpace
import Definitions.Def_TarchaBraids_HalfTwist
import Theorems.Thm_TarchaBraids_pureBraid_le_halfTwist_closure

open BraidsLinksMCG TarchaBraids

theorem solution (n : ℕ) :
    Subgroup.map (FundamentalGroup.map (configProj (n + 1)) (baseOrdered (n + 1)))
        (FundamentalGroup.mapOfEq (configForget n) (configForget_base n)).ker
      ≤ Subgroup.closure
          (Set.range (fun i : Fin (n + 1 - 1) => halfTwistBraid (n + 1) i)) :=
  (Subgroup.map_le_range _ _).trans (TarchaBraids.pureBraid_le_halfTwist_closure (n + 1))
