-- Prove2me | solution 1 for BSLambda.IsDRTournamentWith.card_middles
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T00:57:12.90133+00:00
-- url     : https://prove2.me/submissions/cc9f2b9a-0575-4ba5-8395-2e53890c82bd

module
public import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
public import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
public import Mathlib.Data.Fintype.Card
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_Defs_Tournament
public import Theorems.Thm_BSLambda_IsDRTournamentWith_card_middles_add_add_one
public import Theorems.Thm_BSLambda_IsDRTournamentWith_d_eq_two_mul_t_add_one

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
theorem _root_.solution [Nontrivial ι] (huv : Arc u v) : (middles Arc u v).card = t := by
  have h1 := h.card_middles_add_add_one huv
  have h2 := h.d_eq_two_mul_t_add_one
  omega
end BSLambda.IsDRTournamentWith
