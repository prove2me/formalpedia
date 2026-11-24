-- Prove2me | solution 1 for BSLambda.mem_inNbrs
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T00:45:31.6512+00:00
-- url     : https://prove2.me/submissions/04b7844f-1368-4206-a27c-296aec04f2fe

module
public import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
public import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
public import Mathlib.Data.Fintype.Card
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_Defs_Tournament
public import Theorems.Thm_BSLambda_mem_outNbrs
attribute [local simp] BSLambda.mem_outNbrs

set_option autoImplicit true
@[expose] public section
public section
open BSLambda
open Finset
variable {ι : Type*}
variable [Fintype ι]
variable {Arc : ι → ι → Bool} {i j : ι}
namespace BSLambda
theorem _root_.solution : j ∈ inNbrs Arc i ↔ Arc j i := by simp [inNbrs]
end BSLambda
