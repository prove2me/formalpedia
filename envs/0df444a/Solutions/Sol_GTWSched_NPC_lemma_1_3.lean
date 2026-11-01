-- Prove2me | solution 3 for GTWSched.NPC.lemma_1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-10-31T13:13:53.979788+00:00
-- url     : https://prove2.me/submissions/2a8579f5-d677-436e-83b5-764a9fe012f5
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_CookPvsNP_defs
import Definitions.Def_ProjSchedTW_Complexity_Encoding
import Definitions.Def_GTWSched_NPC_Schedules
import Definitions.Def_GTWSched_NPC_Problems
import Theorems.Thm_CookPvsNP_npComplete_of_polyReducible
import Theorems.Thm_GTWSched_NPC_evenOdd_mem_NP
import Theorems.Thm_GTWSched_NPC_positivePartition_polyReducible_evenOdd

open GTWSched.NPC CookPvsNP ProjSchedTW.Complexity

theorem solution (hP : NPComplete positivePartitionLang) : NPComplete evenOddLang :=
  npComplete_of_polyReducible positivePartitionLang evenOddLang hP evenOdd_mem_NP
    positivePartition_polyReducible_evenOdd
