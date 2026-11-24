-- Prove2me | solution 1 for BSLambda.PartialAssign.indUnion_eq_true_of_sat
-- status  : ACCEPTED   (prove)
-- author  : @sockpaprika
-- created : 2026-11-24T00:52:08.363708+00:00
-- url     : https://prove2.me/submissions/b549580d-e642-4168-af23-7f60e0c900e1

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


theorem solution {i : ι} (h : (P i).Sat x) : indUnion P x = true := by
  simpa [indUnion] using (show ∃ j, (P j).Sat x from ⟨i,h⟩)
