-- Prove2me | solution 2 for BSLambda.Construction.cert_apply_of_fst_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T01:06:06.363171+00:00
-- url     : https://prove2.me/submissions/4c485bd1-1ecf-49a9-96ef-b99209cc555a

module
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_Defs_Sensitivity
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_Defs_Subcube
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_Defs_Tournament
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_Construction_Basic
public import Theorems.Thm_BSLambda_Construction_cert_eq_some_iff

set_option autoImplicit true
@[expose] public section
public section
open BSLambda
open BSLambda.Construction
variable {ι : Type*} {r : ℕ}
variable [DecidableEq ι]
variable {Arc : ι → ι → Bool} {γ : ι → ι → Fin r} {i j : ι} {v : Coord ι r} {b : Bool}
namespace BSLambda.Construction
theorem _root_.solution (h : v.1 = i) : cert Arc γ i v = some true :=
  cert_eq_some_iff.2 (Or.inl ⟨h, rfl⟩)
end BSLambda.Construction
