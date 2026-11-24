-- Prove2me | solution 1 for BSLambda.PartialAssign.exists_conflict_of_forall_not_sat
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T01:40:48.838731+00:00
-- url     : https://prove2.me/submissions/ca1d1c4c-63ff-4426-ba27-6056f0c65e34

module
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_Defs_Cube
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_Defs_Subcube
public import Theorems.Thm_BSLambda_PartialAssign_exists_sat_and_sat_of_forall_not_conflict

set_option autoImplicit true
@[expose] public section
public section
open BSLambda
open BSLambda.PartialAssign
variable {V : Type*}
namespace BSLambda.PartialAssign
theorem _root_.solution {P Q : PartialAssign V}
    (h : ∀ x : Input V, P.Sat x → ¬ Q.Sat x) : ∃ v, P.Conflict Q v := by
  by_contra hc
  obtain ⟨x, hx, hx'⟩ := exists_sat_and_sat_of_forall_not_conflict (not_exists.1 hc)
  exact h x hx hx'
end BSLambda.PartialAssign
