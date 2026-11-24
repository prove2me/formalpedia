-- Prove2me | solution 1 for FairChores.cost_swapOutcomeC
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T03:26:41.776894+00:00
-- url     : https://prove2.me/submissions/5fe5abfd-2657-47f0-88aa-353f6a50b5b8

import Mathlib
import Definitions.Def_RequestProject_ChoresMMSPartition
import Definitions.Def_RequestProject_ChoresPreAlloc
import Definitions.Def_RequestProject_ChoresTwoAgents

set_option autoImplicit true
open scoped BigOperators
open FairChores
variable {T : Type*} [Fintype T] [DecidableEq T]
omit [Fintype T] [DecidableEq T]
namespace FairChores
theorem _root_.solution (c : T → ℝ) (o : Outcome T 2) (j : Fin 2) :
    cost c (swapOutcomeC o) j = cost c o (Equiv.swap 0 1 j) := rfl
end FairChores
