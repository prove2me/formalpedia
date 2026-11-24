-- Prove2me | solution 1 for BSLambda.Construction.ind_eq_false_iff
-- status  : ACCEPTED   (prove)
-- author  : @sockpaprika
-- created : 2026-11-24T00:48:23.976416+00:00
-- url     : https://prove2.me/submissions/c42787a7-41ed-425a-9f59-e2cac85d0811

module
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_Defs_Sensitivity
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_Defs_Subcube
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_Defs_Tournament
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_Construction_Basic
set_option autoImplicit true
@[expose] public section
public section
open BSLambda
open BSLambda.Construction
variable {ι : Type*} {r : ℕ}
variable [Fintype ι] [DecidableEq ι] {Arc : ι → ι → Bool} {γ : ι → ι → Fin r} {i : ι}
variable {x : Input (Coord ι r)}


theorem solution : ind Arc γ x = false ↔ ∀ i, ¬ (cert Arc γ i).Sat x := by
  simp [ind, PartialAssign.indUnion]
