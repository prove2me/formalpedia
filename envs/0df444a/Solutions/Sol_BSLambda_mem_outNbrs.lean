-- Prove2me | solution 1 for BSLambda.mem_outNbrs
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T00:45:06.525813+00:00
-- url     : https://prove2.me/submissions/8bac9f9c-2343-4a3e-bdea-7a7809ccc027

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
variable {Arc : ι → ι → Bool} {i j : ι}
namespace BSLambda
theorem _root_.solution : j ∈ outNbrs Arc i ↔ Arc i j := by simp [outNbrs]
end BSLambda
