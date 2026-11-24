-- Prove2me | solution 1 for FairChores.maxCostData_mono
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T03:25:09.667951+00:00
-- url     : https://prove2.me/submissions/726d3c75-e50a-43e2-8f9c-b207354c6836

import Mathlib
import Definitions.Def_RequestProject_ChoresModel
import Definitions.Def_RequestProject_ChoresMMSPartition

set_option autoImplicit true
open scoped BigOperators
open FairChores
variable {T : Type*} [Fintype T] [DecidableEq T] {n : ℕ}
omit [DecidableEq T]
namespace FairChores
theorem _root_.solution (c : T → ℝ) (assign : T → Option (Fin n)) {m m' : Fin n → ℝ}
    (h : ∀ j, m j ≤ m' j) : maxCostData c assign m ≤ maxCostData c assign m' :=
  ciSup_mono (Finite.bddAbove_range _) (fun j => by linarith [h j])
end FairChores
