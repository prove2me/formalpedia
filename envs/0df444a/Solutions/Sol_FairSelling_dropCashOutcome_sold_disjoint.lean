-- Prove2me | solution 1 for FairSelling.dropCashOutcome_sold_disjoint
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T02:56:57.771902+00:00
-- url     : https://prove2.me/submissions/111c2f0c-dfb4-459a-ad23-2681b115ad1d

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
    (h : ∀ i, Disjoint o.sold (o.kept i)) :
    ∀ i, Disjoint (dropCashOutcome o).sold ((dropCashOutcome o).kept i) := by
  exact fun i => optionGoods_disjoint ( h i )
end FairSelling
