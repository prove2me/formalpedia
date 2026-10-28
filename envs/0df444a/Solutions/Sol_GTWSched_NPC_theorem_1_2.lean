-- Prove2me | solution 2 for GTWSched.NPC.theorem_1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-10-28T08:18:43.752012+00:00
-- url     : https://prove2.me/submissions/e60db386-e3f4-4412-b30b-5e54d6714955
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_CookPvsNP_defs
import Definitions.Def_ProjSchedTW_Complexity_Encoding
import Definitions.Def_GTWSched_NPC_Schedules
import Definitions.Def_GTWSched_NPC_Problems
import Theorems.Thm_CookPvsNP_npComplete_of_polyReducible
import Theorems.Thm_GTWSched_NPC_lemma_1
import Theorems.Thm_GTWSched_NPC_td_mem_NP
import Theorems.Thm_GTWSched_NPC_evenOdd_polyReducible_td

open CookPvsNP ProjSchedTW.Complexity GTWSched.NPC

/-- THEOREM 1, p. 336, relative to the NP-completeness of PARTITION: the total discrepancy problem
is NP-complete. -/
theorem solution (hP : NPComplete positivePartitionLang) : NPComplete tdLang :=
  npComplete_of_polyReducible evenOddLang tdLang (lemma_1 hP)
    td_mem_NP evenOdd_polyReducible_td
