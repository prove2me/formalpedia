-- Prove2me | solution 1 for BSLambda.Construction.disjoint_cube_cert
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T01:41:59.66575+00:00
-- url     : https://prove2.me/submissions/c6a2ad42-6238-463d-bf35-7a3dfe372530

module
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_Construction_Basic
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_Construction_Conflict
public import Theorems.Thm_BSLambda_Construction_exists_conflict_of_ne
public import Theorems.Thm_BSLambda_PartialAssign_Conflict_disjoint_cube


set_option autoImplicit true
@[expose] public section
public section
open BSLambda
open BSLambda.Construction
variable {ι : Type*} {r : ℕ}
variable [Fintype ι] [DecidableEq ι] {Arc : ι → ι → Bool} {γ : ι → ι → Fin r} {i j : ι}
namespace BSLambda.Construction
theorem _root_.solution (hT : IsTournament Arc) (hij : i ≠ j) :
    Disjoint (cert Arc γ i).cube (cert Arc γ j).cube :=
  (exists_conflict_of_ne hT hij).elim fun _ hv ↦ hv.disjoint_cube
end BSLambda.Construction
