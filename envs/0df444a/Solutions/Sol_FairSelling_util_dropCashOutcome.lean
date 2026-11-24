-- Prove2me | solution 1 for FairSelling.util_dropCashOutcome
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T02:58:19.536502+00:00
-- url     : https://prove2.me/submissions/87f26a20-1896-46e1-b836-099604f2bc9f

import Mathlib
import Definitions.Def_RequestProject_ThreeAgentCash
import Definitions.Def_RequestProject_ThreeAgentCashComposition
import Theorems.Thm_FairSelling_sum_cashVal_optionGoods

set_option autoImplicit true
open scoped BigOperators
set_option maxHeartbeats 4000000
set_option maxRecDepth 4000
open FairSelling
variable {G : Type*} [Fintype G] [DecidableEq G]
namespace FairSelling
theorem _root_.solution (R : Finset G) (w : G → ℝ)
    (o : Outcome (Option G) 2) (i : Fin 2) :
    util (restrictVal R w) (dropCashOutcome o) i = util (cashVal R w) o i := by
  unfold util;
  rw [ ← sum_cashVal_optionGoods ];
  rfl
end FairSelling
