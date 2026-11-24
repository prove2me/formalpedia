-- Prove2me | solution 1 for FairChores.maxCost_assignOutcome
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T03:25:00.052462+00:00
-- url     : https://prove2.me/submissions/05b13e40-83df-41f2-b137-1ccd39d730a5

import Mathlib
import Definitions.Def_RequestProject_ChoresModel
import Definitions.Def_RequestProject_ChoresMMSPartition

set_option autoImplicit true
open scoped BigOperators
open FairChores
variable {T : Type*} [Fintype T] [DecidableEq T] {n : ℕ}
omit [DecidableEq T]
namespace FairChores
theorem _root_.solution (c : T → ℝ) (assign : T → Option (Fin n)) (m : Fin n → ℝ) :
    maxCost c (assignOutcome assign m) = maxCostData c assign m := rfl
end FairChores
