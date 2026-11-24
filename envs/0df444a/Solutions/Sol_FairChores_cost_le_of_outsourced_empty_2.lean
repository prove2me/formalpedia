-- Prove2me | solution 2 for FairChores.cost_le_of_outsourced_empty
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T03:52:32.568836+00:00
-- url     : https://prove2.me/submissions/8d77d093-7928-4d87-811a-0b2296623cbf

import Mathlib
import Definitions.Def_RequestProject_ChoresModel
import Theorems.Thm_FairChores_mem_outsourced_of_lt_cost

set_option autoImplicit true
open scoped BigOperators
open FairChores
variable {T : Type*} [Fintype T] [DecidableEq T]
variable {n : ℕ}
variable {c p : T → ℝ}
namespace FairChores
theorem _root_.solution {o : Outcome T n} (hvalid : o.Valid p) (hc : ∀ t, 0 ≤ c t)
    (hempty : o.outsourced = ∅) {r : ℝ} (hle : ∀ j, cost c o j ≤ r) (t : T) : c t ≤ r := by
  by_contra hgt
  have hmem := mem_outsourced_of_lt_cost hvalid hc hle (not_le.mp hgt)
  rw [hempty] at hmem
  exact absurd hmem (Finset.notMem_empty t)
end FairChores
