-- Prove2me | solution 1 for BSLambda.Construction.ind_eq_true_of_sat
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T01:12:03.470147+00:00
-- url     : https://prove2.me/submissions/bddd7989-01d6-46cc-804a-3b1e5aed24bd

module
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_Defs_Sensitivity
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_Defs_Subcube
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_Defs_Tournament
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_Construction_Basic
public import Theorems.Thm_BSLambda_PartialAssign_indUnion_eq_true_of_sat


set_option autoImplicit true
@[expose] public section
public section
open BSLambda
open BSLambda.Construction
variable {ι : Type*} {r : ℕ}
variable [Fintype ι] [DecidableEq ι] {Arc : ι → ι → Bool} {γ : ι → ι → Fin r} {i : ι}
variable {x : Input (Coord ι r)}
namespace BSLambda.Construction
theorem _root_.solution (h : (cert Arc γ i).Sat x) : ind Arc γ x = true :=
  PartialAssign.indUnion_eq_true_of_sat h
end BSLambda.Construction
