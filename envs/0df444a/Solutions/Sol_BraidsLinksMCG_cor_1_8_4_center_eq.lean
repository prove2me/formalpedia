-- Prove2me | solution 1 for BraidsLinksMCG.cor_1_8_4_center_eq
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-21T20:09:34.129908+00:00
-- url     : https://prove2.me/submissions/9802d41f-91e3-43f2-b8c6-2f896743d564
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_BraidsLinksMCG_center_le_zpowers_full_twist
import Theorems.Thm_TarchaBraids_prop_3_16_full_twist_mem_center
import Definitions.Def_BraidsLinksMCG_ArtinBraidGroup
import Definitions.Def_BraidsLinksMCG_ArtinEndo

set_option maxRecDepth 100000
set_option maxHeartbeats 1000000
set_option linter.all false

open BraidsLinksMCG

theorem _root_.solution (n : ℕ) (hn : 3 ≤ n) :
    Subgroup.center (ArtinBraidGroup n) = Subgroup.zpowers (sigmaProd n ^ n) :=
  le_antisymm (BraidsLinksMCG.center_le_zpowers_full_twist n hn)
    (Subgroup.zpowers_le.mpr (TarchaBraids.prop_3_16_full_twist_mem_center n))

#print axioms solution
