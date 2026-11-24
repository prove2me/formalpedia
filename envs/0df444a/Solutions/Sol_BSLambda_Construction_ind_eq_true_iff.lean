-- Prove2me | solution 1 for BSLambda.Construction.ind_eq_true_iff
-- status  : ACCEPTED   (prove)
-- author  : @grencez
-- created : 2026-11-24T00:48:22.962717+00:00
-- url     : https://prove2.me/submissions/dfe7eafd-3511-46a9-b50f-50a6ea5cea57

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


theorem solution : ind Arc γ x = true ↔ ∃ i, (cert Arc γ i).Sat x := by
  simp [ind, PartialAssign.indUnion]
