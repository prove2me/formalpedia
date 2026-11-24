-- Prove2me | solution 1 for BSLambda.PartialAssign.sat_unique_of_conflict
-- status  : ACCEPTED   (prove)
-- author  : @sockpaprika
-- created : 2026-11-24T00:52:11.90432+00:00
-- url     : https://prove2.me/submissions/7c1cd622-b168-42d4-8171-9631e5fc91fb

module
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_Defs_Cube
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_Defs_Subcube
set_option autoImplicit true
@[expose] public section
public section
open BSLambda
open BSLambda.PartialAssign
variable {V : Type*}


theorem solution {ι : Type*} {P : ι → PartialAssign V}
    (h : Pairwise fun i j ↦ ∃ v, (P i).Conflict (P j) v) {i j : ι} {x : Input V}
    (hi : (P i).Sat x) (hj : (P j).Sat x) : i = j := by
  by_contra ne
  obtain ⟨v,b,hb,hc⟩ := h ne
  have eq := (hi v b hb).symm.trans (hj v (!b) hc)
  cases b <;> simp at eq
