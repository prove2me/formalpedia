-- Prove2me | solution 2 for BSLambda.PartialAssign.sat_unique_of_conflict
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T01:03:57.610976+00:00
-- url     : https://prove2.me/submissions/ffbb7cd2-43fe-46cb-af7d-ba847de6fc7c

module
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_Defs_Cube
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_Defs_Subcube
public import Theorems.Thm_BSLambda_PartialAssign_Conflict_ne

set_option autoImplicit true
@[expose] public section
public section
open BSLambda
open BSLambda.PartialAssign
variable {V : Type*}
namespace BSLambda.PartialAssign
theorem _root_.solution {ι : Type*} {P : ι → PartialAssign V}
    (h : Pairwise fun i j ↦ ∃ v, (P i).Conflict (P j) v) {i j : ι} {x : Input V}
    (hi : (P i).Sat x) (hj : (P j).Sat x) : i = j := by
  by_contra hij
  obtain ⟨v, hv⟩ := h hij
  exact hv.ne hi hj rfl
end BSLambda.PartialAssign
