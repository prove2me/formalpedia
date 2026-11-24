-- Prove2me | solution 1 for BSLambda.sum_card_outNbrs_eq_sum_card_inNbrs
-- status  : ACCEPTED   (prove)
-- author  : @sockpaprika
-- created : 2026-11-24T00:53:48.642853+00:00
-- url     : https://prove2.me/submissions/ebec9252-83a3-4cf8-b0fa-def16bf76030

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
variable (Arc)


theorem solution :
    ∑ x, (outNbrs Arc x).card = ∑ x, (inNbrs Arc x).card := by
  classical
  simp only [outNbrs,inNbrs,Finset.card_filter]
  rw [Finset.sum_comm]
