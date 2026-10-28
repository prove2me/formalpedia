-- Prove2me | solution 1 for GTWSched.NPC.lemma_1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-10-27T07:04:35.893486+00:00
-- url     : https://prove2.me/submissions/1b716048-2aec-4d59-a034-6f506757055d
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_CookPvsNP_defs
import Definitions.Def_ProjSchedTW_Complexity_Encoding
import Definitions.Def_GTWSched_NPC_Schedules
import Definitions.Def_GTWSched_NPC_Problems
import Theorems.Thm_CookPvsNP_npComplete_of_polyReducible
import Theorems.Thm_GTWSched_NPC_evenOdd_mem_NP
import Theorems.Thm_GTWSched_NPC_positivePartition_polyReducible_evenOdd

set_option autoImplicit false

open CookPvsNP ProjSchedTW.Complexity GTWSched.NPC

theorem solution (hP : NPComplete positivePartitionLang) : NPComplete evenOddLang :=
  npComplete_of_polyReducible positivePartitionLang evenOddLang
    hP evenOdd_mem_NP positivePartition_polyReducible_evenOdd
