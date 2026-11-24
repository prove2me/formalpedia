-- Prove2me | solution 1 for FairSelling.dropCashOutcome_kept_disjoint
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T02:57:50.712445+00:00
-- url     : https://prove2.me/submissions/79a69343-bb32-443a-a4fd-9291770d0843

import Mathlib
import Definitions.Def_RequestProject_ThreeAgentCash
import Definitions.Def_RequestProject_ThreeAgentCashComposition
import Theorems.Thm_FairSelling_optionGoods_disjoint

set_option autoImplicit true
open scoped BigOperators
set_option maxHeartbeats 4000000
set_option maxRecDepth 4000
open FairSelling
variable {G : Type*} [Fintype G] [DecidableEq G]
namespace FairSelling
theorem _root_.solution (o : Outcome (Option G) 2)
    (h : ∀ i j, i ≠ j → Disjoint (o.kept i) (o.kept j)) :
    ∀ i j, i ≠ j → Disjoint ((dropCashOutcome o).kept i) ((dropCashOutcome o).kept j) := by
  exact fun i j hij => optionGoods_disjoint ( h i j hij )
end FairSelling
