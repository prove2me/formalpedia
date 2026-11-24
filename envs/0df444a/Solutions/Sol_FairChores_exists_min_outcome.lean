-- Prove2me | solution 1 for FairChores.exists_min_outcome
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T03:27:47.502908+00:00
-- url     : https://prove2.me/submissions/b343dd7d-b43d-4fa9-bb75-24ed9932dcce

import Mathlib
import Definitions.Def_RequestProject_ChoresModel
import Definitions.Def_RequestProject_ChoresMMSPartition
import Theorems.Thm_FairChores_maxCost_assignOutcome
import Theorems.Thm_FairChores_assignOutcome_valid
import Theorems.Thm_FairChores_exists_opt_money
import Theorems.Thm_FairChores_exists_assignform_le

set_option autoImplicit true
open scoped BigOperators
open FairChores
variable {T : Type*} [Fintype T] [DecidableEq T] {n : ℕ}
namespace FairChores
theorem _root_.solution (c p : T → ℝ) (hp : ∀ t, 0 ≤ p t) (hn : 0 < n) :
    ∃ o : Outcome T n, o.Valid p ∧ ∀ o' : Outcome T n, o'.Valid p → maxCost c o ≤ maxCost c o' := by
  classical
  choose m hm using fun assign => exists_opt_money c p hp hn assign
  obtain ⟨a0, ha0⟩ := Finite.exists_min
    (fun assign : T → Option (Fin n) => maxCostData c assign (m assign))
  refine ⟨assignOutcome a0 (m a0),
    assignOutcome_valid p a0 (m a0) (hm a0).1 (hm a0).2.1, ?_⟩
  intro o' ho'
  obtain ⟨assign', m', hm0', hms', hle'⟩ := exists_assignform_le hn c p o' ho'
  calc maxCost c (assignOutcome a0 (m a0)) = maxCostData c a0 (m a0) :=
        maxCost_assignOutcome c a0 (m a0)
    _ ≤ maxCostData c assign' (m assign') := ha0 assign'
    _ ≤ maxCostData c assign' m' := (hm assign').2.2 m' hm0' hms'
    _ ≤ maxCost c o' := hle'
end FairChores
