-- Prove2me | solution 2 for BSLambda.sum_card_outNbrs_eq_sum_card_inNbrs
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T00:55:40.40381+00:00
-- url     : https://prove2.me/submissions/257c5a0f-e4c2-4fb9-a635-75868b622d30

module
public import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
public import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
public import Mathlib.Data.Fintype.Card
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_Defs_Tournament
public import Theorems.Thm_BSLambda_mem_outNbrs
public import Theorems.Thm_BSLambda_mem_inNbrs
attribute [local simp] BSLambda.mem_outNbrs
attribute [local simp] BSLambda.mem_inNbrs

set_option autoImplicit true
@[expose] public section
public section
open BSLambda
open Finset
variable {ι : Type*}
variable [Fintype ι]
variable {Arc : ι → ι → Bool} {i j : ι}
variable (Arc)
namespace BSLambda
theorem _root_.solution :
    ∑ x, (outNbrs Arc x).card = ∑ x, (inNbrs Arc x).card := by
  simp only [outNbrs, inNbrs, card_filter]
  exact sum_comm
end BSLambda
