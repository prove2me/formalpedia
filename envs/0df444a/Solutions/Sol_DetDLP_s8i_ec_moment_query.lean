-- Prove2me | solution 1 for DetDLP.s8i_ec_moment_query
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Bingsheng
-- created : 2026-11-24T13:48:06.174194+00:00
-- url     : https://prove2.me/submissions/b57eccf9-0295-4636-badc-b6a5e0cb5321
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_DetDLP_S8I_ECMomentGraph
import Definitions.Def_DetDLP_S8C_TagSpec
import Theorems.Thm_DetDLP_s8i_ec_moment_realizes

set_option autoImplicit false

open DetDLP

/--
Sketch of tag-2 (EC moment) Stage I query machines via `S8I.ECMoment.tagIntro`.
Child lemma `s8i_ec_moment_realizes` supplies the per-word `Realizes` obligations.
-/
theorem solution (h : DetDLP.S8C.GadgetLaws) : DetDLP.S8C.TagSpec [2] := by
  obtain ⟨make, port, L, hm, he, hR⟩ := s8i_ec_moment_realizes h
  exact DetDLP.S8I.ECMoment.tagIntro make port L hm he hR
