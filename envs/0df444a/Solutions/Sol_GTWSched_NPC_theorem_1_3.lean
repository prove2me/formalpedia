-- Prove2me | solution 3 for GTWSched.NPC.theorem_1
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-10-31T13:13:54.559489+00:00
-- url     : https://prove2.me/submissions/d0fc57f6-2e5a-4ad2-a7a1-9b4071fb824b

import Mathlib
import Definitions.Def_CookPvsNP_defs
import Definitions.Def_ProjSchedTW_Complexity_Encoding
import Definitions.Def_GTWSched_NPC_Schedules
import Definitions.Def_GTWSched_NPC_Problems
import Theorems.Thm_CookPvsNP_npComplete_of_polyReducible
import Theorems.Thm_GTWSched_NPC_lemma_1
import Theorems.Thm_GTWSched_NPC_td_mem_NP
import Theorems.Thm_GTWSched_NPC_evenOdd_polyReducible_td

open GTWSched.NPC CookPvsNP ProjSchedTW.Complexity

theorem solution (hP : NPComplete positivePartitionLang) : NPComplete tdLang :=
  npComplete_of_polyReducible evenOddLang tdLang (lemma_1 hP) td_mem_NP
    evenOdd_polyReducible_td
