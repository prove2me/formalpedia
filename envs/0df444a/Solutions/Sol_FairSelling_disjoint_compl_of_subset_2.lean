-- Prove2me | solution 2 for FairSelling.disjoint_compl_of_subset
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T02:59:39.39074+00:00
-- url     : https://prove2.me/submissions/71c1dd49-bf4f-47f0-9bc1-2fe5a4b100d5

import Mathlib
import Definitions.Def_RequestProject_CanonicalPartition
import Definitions.Def_RequestProject_Matching
import Definitions.Def_RequestProject_ThreeAgentCashComposition
import Definitions.Def_RequestProject_MatchingPhase

set_option autoImplicit true
open scoped BigOperators
set_option maxHeartbeats 1000000
set_option maxRecDepth 4000
open FairSelling
variable {G : Type*} [Fintype G] [DecidableEq G]
namespace FairSelling
theorem _root_.solution {Y U : Finset G} (hYU : Y ⊆ U) :
    Disjoint Y (Finset.univ \ U) := by
  refine Finset.disjoint_left.mpr (fun x hx hx' => ?_)
  exact (Finset.mem_sdiff.mp hx').2 (hYU hx)
end FairSelling
