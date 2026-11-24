-- Prove2me | solution 1 for BSLambda.mem_commonIn
-- status  : ACCEPTED   (prove)
-- author  : @sockpaprika
-- created : 2026-11-24T00:47:09.158786+00:00
-- url     : https://prove2.me/submissions/64fddb18-61dc-4592-835e-7eec837baf82

module
public import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
public import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
public import Mathlib.Data.Fintype.Card
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_Defs_Tournament
set_option autoImplicit true
@[expose] public section
public section
open BSLambda
open Finset
variable {ι : Type*}
variable [Fintype ι]
variable [DecidableEq ι]
variable {Arc : ι → ι → Bool} {i j l u v : ι}


theorem solution : l ∈ commonIn Arc i j ↔ Arc l i ∧ Arc l j := by
  simp [commonIn, outNbrs, inNbrs]
