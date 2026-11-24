-- Prove2me | solution 1 for BSLambda.sum_card_commonOut_eq_sum_card_middles
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T00:55:59.272271+00:00
-- url     : https://prove2.me/submissions/f8630546-5cb7-457b-b657-bbe96f83e291

module
public import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
public import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
public import Mathlib.Data.Fintype.Card
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_Defs_Tournament
public import Theorems.Thm_BSLambda_mem_outNbrs
public import Theorems.Thm_BSLambda_mem_inNbrs
public import Theorems.Thm_BSLambda_mem_commonOut
public import Theorems.Thm_BSLambda_mem_commonIn
public import Theorems.Thm_BSLambda_mem_middles
attribute [local simp] BSLambda.mem_outNbrs
attribute [local simp] BSLambda.mem_inNbrs
attribute [local simp] BSLambda.mem_commonOut
attribute [local simp] BSLambda.mem_commonIn
attribute [local simp] BSLambda.mem_middles

set_option autoImplicit true
@[expose] public section
public section
open BSLambda
open Finset
variable {ι : Type*}
variable [Fintype ι]
variable [DecidableEq ι]
variable {Arc : ι → ι → Bool} {i j l u v : ι}
variable (Arc u)
namespace BSLambda
theorem _root_.solution :
    ∑ y ∈ outNbrs Arc u, (commonOut Arc u y).card
      = ∑ y ∈ outNbrs Arc u, (middles Arc u y).card := by
  simp only [commonOut, middles, ← filter_mem_eq_inter, card_filter, mem_outNbrs, mem_inNbrs]
  exact sum_comm
end BSLambda
