-- Prove2me | solution 1 for BSLambda.PartialAssign.indUnion_eq_false_iff
-- status  : ACCEPTED   (prove)
-- author  : @grencez
-- created : 2026-11-24T00:47:11.204751+00:00
-- url     : https://prove2.me/submissions/0e88befb-e902-4dd3-a1bb-b707baf8d502

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


theorem solution : indUnion P x = false ↔ ∀ i, ¬ (P i).Sat x := by
  simp [indUnion]
