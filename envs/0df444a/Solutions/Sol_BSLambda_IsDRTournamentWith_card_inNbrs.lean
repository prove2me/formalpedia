-- Prove2me | solution 1 for BSLambda.IsDRTournamentWith.card_inNbrs
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T00:57:22.186009+00:00
-- url     : https://prove2.me/submissions/6bd662e9-334c-451e-8fe4-9afe0a674866

module
public import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
public import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
public import Mathlib.Data.Fintype.Card
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_Defs_Tournament
public import Theorems.Thm_BSLambda_sum_card_outNbrs_eq_sum_card_inNbrs
public import Theorems.Thm_BSLambda_IsTournament_card_outNbrs_add_card_inNbrs

set_option autoImplicit true
@[expose] public section
public section
open BSLambda
open Finset
variable {ι : Type*}
variable [Fintype ι]
variable [DecidableEq ι]
open BSLambda.IsDRTournamentWith
variable {Arc : ι → ι → Bool} {d t : ℕ} (h : IsDRTournamentWith Arc d t) {u v : ι}
include h
namespace BSLambda.IsDRTournamentWith
theorem _root_.solution (i : ι) : (inNbrs Arc i).card = d := by
  have hall (x : ι) : (inNbrs Arc x).card = (inNbrs Arc i).card := by
    have h1 := h.card_outNbrs_add_card_inNbrs x
    have h2 := h.card_outNbrs_add_card_inNbrs i
    rw [h.card_outNbrs] at h1 h2
    omega
  have hsum := sum_card_outNbrs_eq_sum_card_inNbrs Arc
  rw [sum_const_nat fun x _ ↦ h.card_outNbrs x, sum_const_nat fun x _ ↦ hall x, card_univ] at hsum
  exact (Nat.eq_of_mul_eq_mul_left (Fintype.card_pos_iff.2 ⟨i⟩) hsum).symm
end BSLambda.IsDRTournamentWith
