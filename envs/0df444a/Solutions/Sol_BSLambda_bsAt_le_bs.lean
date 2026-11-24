-- Prove2me | solution 1 for BSLambda.bsAt_le_bs
-- status  : ACCEPTED   (prove)
-- author  : @grencez
-- created : 2026-11-24T00:53:50.529159+00:00
-- url     : https://prove2.me/submissions/1387fe40-1124-4955-ab9b-2e546e0ee974

module
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_Defs_Cube
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_Defs_Sensitivity
set_option autoImplicit true
@[expose] public section
public section
open BSLambda
variable {V : Type*} [Fintype V] [DecidableEq V]


theorem solution (f : Input V → Bool) (x : Input V) : bsAt f x ≤ bs f := by
  exact Finset.le_sup (f := bsAt f) (Finset.mem_univ x)
