-- Prove2me | solution 1 for BSLambda.PartialAssign.exists_sat_and_sat_of_forall_not_conflict
-- status  : ACCEPTED   (prove)
-- author  : @sockpaprika
-- created : 2026-11-24T00:54:00.012039+00:00
-- url     : https://prove2.me/submissions/c3360bce-eff8-4b7f-bc29-2fc31fe3e0ae

module
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_Defs_Cube
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_Defs_Subcube
set_option autoImplicit true
@[expose] public section
public section
open BSLambda
open BSLambda.PartialAssign
variable {V : Type*}


theorem solution {P Q : PartialAssign V}
    (h : ∀ v, ¬ P.Conflict Q v) : ∃ x : Input V, P.Sat x ∧ Q.Sat x := by
  refine ⟨fun v => (P v).getD ((Q v).getD false), ?_, ?_⟩
  · intro v b e; simp [e]
  · intro v b e; cases ep : P v with
    | none => simp [ep,e]
    | some a =>
      have hh := h v
      cases a <;> cases b <;> simp_all [Conflict]
