-- Prove2me | solution 1 for BSLambda.PartialAssign.violSet_subset_fixedSet
-- status  : ACCEPTED   (prove)
-- author  : @sockpaprika
-- created : 2026-11-24T00:52:10.320687+00:00
-- url     : https://prove2.me/submissions/1e83a216-8aed-4570-8798-7d496ae7bef4

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


theorem solution (P : PartialAssign V) (x : Input V) :
    P.violSet x ⊆ P.fixedSet := by
  intro v h
  cases e : P v <;> simp_all [fixedSet,violSet]
