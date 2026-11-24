-- Prove2me | solution 1 for BSLambda.PartialAssign.indUnion_eq_true_iff
-- status  : ACCEPTED   (prove)
-- author  : @sockpaprika
-- created : 2026-11-24T00:47:12.030562+00:00
-- url     : https://prove2.me/submissions/e7929515-b15c-4209-8ee8-9c7e81267903

module
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_Defs_Cube
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_Defs_Subcube
set_option autoImplicit true
@[expose] public section
public section
open BSLambda
open BSLambda.PartialAssign
variable {V : Type*}
variable [Fintype V]
variable {ι : Type*} [Fintype ι]
variable {P : ι → PartialAssign V} {x : Input V}


theorem solution : indUnion P x = true ↔ ∃ i, (P i).Sat x := by
  simp [indUnion]
