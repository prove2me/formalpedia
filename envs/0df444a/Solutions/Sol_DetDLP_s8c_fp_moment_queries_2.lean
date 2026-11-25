-- Prove2me | solution 2 for DetDLP.s8c_fp_moment_queries
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Bingsheng
-- created : 2026-11-24T19:03:32.844688+00:00
-- url     : https://prove2.me/submissions/9a9fdcc7-24c1-4a3e-a17d-73ca96a91844
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_DetDLP_S8G_FpMomentGraph
import Definitions.Def_DetDLP_S8C_TagSpec
import Theorems.Thm_DetDLP_s8g_fp_moment_realizes

set_option autoImplicit false

open DetDLP
open DetDLP.S8C
open DetDLP.S8G.FpMoment

/--
Sketch of tag-1 (`fp` moment) Stage I query machines.

Paper (Formal Paper, proof of Theorem 3.1): conditional-expectation derandomization evaluates
the four seed-prefix moments \(A_η,B_η,J_η\) (and the completion mass) by BTN contraction.
`s8g_fp_moment_realizes` supplies uniform `PolyT` encoders realizing every such moment count;
`S8G.FpMoment.tagIntro` packages them into `TagSpec [1]`. The `GadgetLaws` hypothesis is
forwarded to the layout/realizes child (arithmetic identities used by the hash gadgets).
-/
theorem solution (h : DetDLP.S8C.GadgetLaws) : DetDLP.S8C.TagSpec [1] := by
  obtain ⟨make, port, L, hm, he, hR⟩ := s8g_fp_moment_realizes h
  exact tagIntro make port L hm he hR
