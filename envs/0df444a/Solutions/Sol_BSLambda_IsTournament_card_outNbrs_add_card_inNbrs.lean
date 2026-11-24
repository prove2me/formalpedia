-- Prove2me | solution 1 for BSLambda.IsTournament.card_outNbrs_add_card_inNbrs
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T00:56:41.919721+00:00
-- url     : https://prove2.me/submissions/64ffeb5e-25ec-43f1-a134-255c6749df60

module
public import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
public import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
public import Mathlib.Data.Fintype.Card
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_Defs_Tournament
public import Theorems.Thm_BSLambda_IsTournament_disjoint_outNbrs_inNbrs
public import Theorems.Thm_BSLambda_IsTournament_outNbrs_union_inNbrs

set_option autoImplicit true
@[expose] public section
public section
open BSLambda
open Finset
variable {ι : Type*}
variable [Fintype ι]
variable [DecidableEq ι]
variable {Arc : ι → ι → Bool} {i j l u v : ι}
open BSLambda.IsTournament
variable (h : IsTournament Arc)
include h
omit [DecidableEq ι]
namespace BSLambda.IsTournament
theorem _root_.solution (v : ι) :
    (outNbrs Arc v).card + (inNbrs Arc v).card + 1 = Fintype.card ι := by
  classical
  rw [← card_univ, ← card_erase_add_one (mem_univ v), ← h.outNbrs_union_inNbrs v,
    card_union_of_disjoint (h.disjoint_outNbrs_inNbrs v)]
end BSLambda.IsTournament
