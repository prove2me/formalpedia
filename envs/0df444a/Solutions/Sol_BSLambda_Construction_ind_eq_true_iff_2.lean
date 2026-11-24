-- Prove2me | solution 2 for BSLambda.Construction.ind_eq_true_iff
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T01:02:26.133312+00:00
-- url     : https://prove2.me/submissions/e2ed31f4-6714-42b8-82a8-62feb852e973

module
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_Defs_Sensitivity
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_Defs_Subcube
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_Defs_Tournament
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_Construction_Basic
public import Theorems.Thm_BSLambda_PartialAssign_indUnion_eq_true_iff
attribute [local simp] BSLambda.PartialAssign.indUnion_eq_true_iff



set_option autoImplicit true
@[expose] public section
public section
open BSLambda
open BSLambda.Construction
variable {ι : Type*} {r : ℕ}
variable [Fintype ι] [DecidableEq ι] {Arc : ι → ι → Bool} {γ : ι → ι → Fin r} {i : ι}
variable {x : Input (Coord ι r)}
namespace BSLambda.Construction
theorem _root_.solution : ind Arc γ x = true ↔ ∃ i, (cert Arc γ i).Sat x :=
  PartialAssign.indUnion_eq_true_iff
end BSLambda.Construction
