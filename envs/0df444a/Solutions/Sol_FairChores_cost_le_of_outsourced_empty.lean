-- Prove2me | solution 1 for FairChores.cost_le_of_outsourced_empty
-- status  : ACCEPTED   (prove)
-- author  : @sockpaprika
-- created : 2026-11-24T03:22:26.685232+00:00
-- url     : https://prove2.me/submissions/7af10bbb-5d80-438b-92ba-8701dc3b9b53

import Mathlib
import Definitions.Def_RequestProject_ChoresModel
set_option autoImplicit true
open scoped BigOperators
open FairChores
variable {T : Type*} [Fintype T] [DecidableEq T]
variable {n : ℕ}
variable {c p : T → ℝ}


theorem solution {o : Outcome T n} (hvalid : o.Valid p) (hc : ∀ t, 0 ≤ c t)
    (hempty : o.outsourced = ∅) {r : ℝ} (hle : ∀ j, cost c o j ≤ r) (t : T) : c t ≤ r := by
  obtain ⟨_,_,cover,pay,_⟩ := hvalid
  rw [hempty, Finset.empty_union] at cover
  have hmem : t ∈ Finset.univ.biUnion o.kept := cover.symm ▸ Finset.mem_univ t
  obtain ⟨j,_,hj⟩ := Finset.mem_biUnion.mp hmem
  have hsum := Finset.single_le_sum (f := c) (fun g _ => hc g) hj
  have H := hle j; unfold cost at H; linarith [pay j]
