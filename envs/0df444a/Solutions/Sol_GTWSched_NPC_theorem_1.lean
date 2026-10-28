-- Prove2me | solution 1 for GTWSched.NPC.theorem_1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-10-27T07:04:36.60969+00:00
-- url     : https://prove2.me/submissions/15863057-d225-4c51-b8aa-49d5999c98a4
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

set_option autoImplicit false

open CookPvsNP ProjSchedTW.Complexity GTWSched.NPC

theorem solution (hP : NPComplete positivePartitionLang) : NPComplete tdLang :=
  npComplete_of_polyReducible evenOddLang tdLang
    (lemma_1 hP) td_mem_NP evenOdd_polyReducible_td
