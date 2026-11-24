-- Prove2me | solution 2 for BSLambda.Construction.conflict_gateCoord
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T01:06:38.863402+00:00
-- url     : https://prove2.me/submissions/6cd0dec6-05aa-48d8-9792-0b2f9a0daa4b

module
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_Construction_Basic
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_Construction_Conflict
public import Theorems.Thm_BSLambda_Construction_cert_apply_gateCoord
public import Theorems.Thm_BSLambda_Construction_cert_apply_of_fst_eq
public import Theorems.Thm_BSLambda_Construction_gateCoord_fst
attribute [local simp] BSLambda.Construction.gateCoord_fst



set_option autoImplicit true
@[expose] public section
public section
open BSLambda
open BSLambda.Construction
variable {ι : Type*} {r : ℕ}
variable [DecidableEq ι] {Arc : ι → ι → Bool} {γ : ι → ι → Fin r} {i j : ι}
namespace BSLambda.Construction
theorem _root_.solution (hji : j ≠ i) (hij : Arc i j) :
    (cert Arc γ i).Conflict (cert Arc γ j) (gateCoord γ i j) :=
  ⟨false, cert_apply_gateCoord hji hij, cert_apply_of_fst_eq (gateCoord_fst γ i j)⟩
end BSLambda.Construction
