-- Prove2me | solution 1 for FairChores.maxCost_le_iff
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T03:24:52.703008+00:00
-- url     : https://prove2.me/submissions/234e61fb-3ff5-41f2-bc5e-976bb8845a46

import Mathlib
import Definitions.Def_RequestProject_ChoresModel
import Definitions.Def_RequestProject_ChoresMMSPartition

set_option autoImplicit true
open scoped BigOperators
open FairChores
variable {T : Type*} [Fintype T] [DecidableEq T] {n : ℕ}
omit [Fintype T] [DecidableEq T]
namespace FairChores
theorem _root_.solution (hn : 0 < n) (c : T → ℝ) (o : Outcome T n) (r : ℝ) :
    maxCost c o ≤ r ↔ ∀ j, cost c o j ≤ r := by
  haveI : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  rw [maxCost, ciSup_le_iff (Finite.bddAbove_range _)]
end FairChores
