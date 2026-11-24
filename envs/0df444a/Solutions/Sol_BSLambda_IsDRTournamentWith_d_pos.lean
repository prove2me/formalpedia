-- Prove2me | solution 1 for BSLambda.IsDRTournamentWith.d_pos
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T00:56:16.72283+00:00
-- url     : https://prove2.me/submissions/19e8ca09-bace-460f-8251-215c26e9f1db

module
public import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
public import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
public import Mathlib.Data.Fintype.Card
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_Defs_Tournament
public import Theorems.Thm_BSLambda_IsTournament_arc_or_arc
public import Theorems.Thm_BSLambda_mem_outNbrs
attribute [local simp] BSLambda.mem_outNbrs

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
theorem _root_.solution [Nontrivial ι] : 0 < d := by
  obtain ⟨a, b, hab⟩ := exists_pair_ne ι
  obtain hb | hb := h.arc_or_arc hab
  exacts [(card_pos.2 ⟨b, mem_outNbrs.2 hb⟩).trans_eq (h.card_outNbrs a),
    (card_pos.2 ⟨a, mem_outNbrs.2 hb⟩).trans_eq (h.card_outNbrs b)]
end BSLambda.IsDRTournamentWith
