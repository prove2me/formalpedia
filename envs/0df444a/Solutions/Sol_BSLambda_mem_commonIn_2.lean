-- Prove2me | solution 2 for BSLambda.mem_commonIn
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T00:47:09.748813+00:00
-- url     : https://prove2.me/submissions/6b606cd5-3f46-4a94-b15d-7af7d4d0652c

module
public import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
public import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
public import Mathlib.Data.Fintype.Card
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_Defs_Tournament
public import Theorems.Thm_BSLambda_mem_outNbrs
public import Theorems.Thm_BSLambda_mem_inNbrs
public import Theorems.Thm_BSLambda_mem_commonOut
attribute [local simp] BSLambda.mem_outNbrs
attribute [local simp] BSLambda.mem_inNbrs
attribute [local simp] BSLambda.mem_commonOut

set_option autoImplicit true
@[expose] public section
public section
open BSLambda
open Finset
variable {ι : Type*}
variable [Fintype ι]
variable [DecidableEq ι]
variable {Arc : ι → ι → Bool} {i j l u v : ι}
namespace BSLambda
theorem _root_.solution : l ∈ commonIn Arc i j ↔ Arc l i ∧ Arc l j := by simp [commonIn]
end BSLambda
