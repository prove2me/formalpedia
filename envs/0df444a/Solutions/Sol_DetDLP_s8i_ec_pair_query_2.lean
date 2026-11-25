-- Prove2me | solution 2 for DetDLP.s8i_ec_pair_query
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Bingsheng
-- created : 2026-11-24T11:16:05.235231+00:00
-- url     : https://prove2.me/submissions/7408408b-cadd-4fc7-befe-d1f7a1ab0326
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_DetDLP_S8M_ECPairGraph
import Definitions.Def_DetDLP_S8C_TagSpec
import Theorems.Thm_DetDLP_s8m_ec_pair_realizes

set_option autoImplicit false

open DetDLP

/--
Sketch of tag-6 (EC pair) Stage I query machines via `S8M.ECPair.tagIntro`.
Child lemma `s8m_ec_pair_realizes` supplies the per-word `Realizes` obligations.
-/
theorem solution (h : DetDLP.S8C.GadgetLaws) : DetDLP.S8C.TagSpec [6] := by
  obtain ⟨make, port, L, hm, he, hR⟩ := s8m_ec_pair_realizes h
  exact DetDLP.S8M.ECPair.tagIntro make port L hm he hR