-- Prove2me | solution 1 for BSLambda.mem_middles
-- status  : ACCEPTED   (prove)
-- author  : @grencez
-- created : 2026-11-24T00:47:09.971694+00:00
-- url     : https://prove2.me/submissions/97ab8e92-cbed-49e2-9d46-7f18c8eb7566

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


theorem solution : l ∈ middles Arc u v ↔ Arc u l ∧ Arc l v := by
  simp [middles, outNbrs, inNbrs]
