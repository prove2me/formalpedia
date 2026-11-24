-- Prove2me | solution 1 for BSLambda.IsDRTournamentWith.card_eq_two_mul_add_one
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T01:41:40.001417+00:00
-- url     : https://prove2.me/submissions/d2e325fc-2a1c-4682-9c74-baceb67ed812

module
public import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
public import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
public import Mathlib.Data.Fintype.Card
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_Defs_Tournament
public import Theorems.Thm_BSLambda_IsTournament_card_outNbrs_add_card_inNbrs
public import Theorems.Thm_BSLambda_IsDRTournamentWith_card_inNbrs

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
theorem _root_.solution [Nonempty ι] : Fintype.card ι = 2 * d + 1 := by
  have hi := h.card_outNbrs_add_card_inNbrs (Classical.arbitrary ι)
  rw [h.card_outNbrs, h.card_inNbrs] at hi
  omega
end BSLambda.IsDRTournamentWith
