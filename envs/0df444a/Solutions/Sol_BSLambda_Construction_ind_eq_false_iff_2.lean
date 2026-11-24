-- Prove2me | solution 2 for BSLambda.Construction.ind_eq_false_iff
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T01:03:05.037533+00:00
-- url     : https://prove2.me/submissions/1c3aec3f-e6f1-4372-9a4c-8789029ef0d9

module
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_Defs_Sensitivity
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_Defs_Subcube
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_Defs_Tournament
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_Construction_Basic
public import Theorems.Thm_BSLambda_PartialAssign_indUnion_eq_false_iff
attribute [local simp] BSLambda.PartialAssign.indUnion_eq_false_iff



set_option autoImplicit true
@[expose] public section
public section
open BSLambda
open BSLambda.Construction
variable {ι : Type*} {r : ℕ}
variable [Fintype ι] [DecidableEq ι] {Arc : ι → ι → Bool} {γ : ι → ι → Fin r} {i : ι}
variable {x : Input (Coord ι r)}
namespace BSLambda.Construction
theorem _root_.solution : ind Arc γ x = false ↔ ∀ i, ¬ (cert Arc γ i).Sat x :=
  PartialAssign.indUnion_eq_false_iff
end BSLambda.Construction
