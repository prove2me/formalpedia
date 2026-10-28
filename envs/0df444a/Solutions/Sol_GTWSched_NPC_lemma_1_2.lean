-- Prove2me | solution 2 for GTWSched.NPC.lemma_1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-10-28T08:18:43.086283+00:00
-- url     : https://prove2.me/submissions/eb754ad5-ce65-459a-8d0b-363641b9c707
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_CookPvsNP_defs
import Definitions.Def_ProjSchedTW_Complexity_Encoding
import Definitions.Def_GTWSched_NPC_Schedules
import Definitions.Def_GTWSched_NPC_Problems
import Theorems.Thm_CookPvsNP_npComplete_of_polyReducible
import Theorems.Thm_GTWSched_NPC_evenOdd_mem_NP
import Theorems.Thm_GTWSched_NPC_positivePartition_polyReducible_evenOdd

open CookPvsNP ProjSchedTW.Complexity GTWSched.NPC

/-- LEMMA 1, p. 333, relative to the NP-completeness of PARTITION: the even-odd partition problem
is NP-complete. -/
theorem solution (hP : NPComplete positivePartitionLang) : NPComplete evenOddLang :=
  npComplete_of_polyReducible positivePartitionLang evenOddLang hP
    evenOdd_mem_NP positivePartition_polyReducible_evenOdd
