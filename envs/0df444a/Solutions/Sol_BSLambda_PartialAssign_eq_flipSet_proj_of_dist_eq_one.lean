-- Prove2me | solution 1 for BSLambda.PartialAssign.eq_flipSet_proj_of_dist_eq_one
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T01:10:47.195528+00:00
-- url     : https://prove2.me/submissions/9d53f024-7729-416f-84b4-4213134e16e8

module
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_Defs_Cube
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_Defs_Subcube
public import Theorems.Thm_BSLambda_PartialAssign_dist_eq_card_violSet
public import Theorems.Thm_BSLambda_PartialAssign_eq_flipSet_proj_violSet

set_option autoImplicit true
@[expose] public section
public section
open BSLambda
open BSLambda.PartialAssign
variable {V : Type*}
variable [Fintype V] [DecidableEq V]
namespace BSLambda.PartialAssign
theorem _root_.solution {P : PartialAssign V} {x : Input V} (hd : P.dist x = 1) :
    ∃ v, P.violSet x = {v} ∧ x = flipSet (P.proj x) {v} := by
  rw [dist_eq_card_violSet] at hd
  obtain ⟨v, hv⟩ := Finset.card_eq_one.1 hd
  exact ⟨v, hv, hv ▸ eq_flipSet_proj_violSet P x⟩
end BSLambda.PartialAssign
