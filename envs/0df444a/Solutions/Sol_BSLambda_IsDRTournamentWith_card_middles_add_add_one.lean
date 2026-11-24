-- Prove2me | solution 1 for BSLambda.IsDRTournamentWith.card_middles_add_add_one
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T00:52:52.837642+00:00
-- url     : https://prove2.me/submissions/10054c71-f746-4e35-9e10-f106176f05d9

module
public import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
public import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
public import Mathlib.Data.Fintype.Card
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_Defs_Tournament
public import Theorems.Thm_BSLambda_IsTournament_ne_of_arc
public import Theorems.Thm_BSLambda_IsTournament_arc_asymm
public import Theorems.Thm_BSLambda_IsTournament_arc_or_arc
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
open BSLambda.IsDRTournamentWith
variable {Arc : ι → ι → Bool} {d t : ℕ} (h : IsDRTournamentWith Arc d t) {u v : ι}
include h
namespace BSLambda.IsDRTournamentWith
theorem _root_.solution (huv : Arc u v) : (middles Arc u v).card + t + 1 = d := by
  have hdisj : Disjoint (middles Arc u v) (commonOut Arc u v) :=
    disjoint_left.2 fun _ hx hx' ↦ h.arc_asymm (mem_middles.1 hx).2 (mem_commonOut.1 hx').2
  have hsplit : outNbrs Arc u = insert v (middles Arc u v ∪ commonOut Arc u v) := by
    ext x
    simp only [mem_insert, mem_union, mem_middles, mem_commonOut, mem_outNbrs]
    constructor
    · exact fun hx ↦ (eq_or_ne x v).imp id fun hne ↦ (h.arc_or_arc hne).imp (⟨hx, ·⟩) (⟨hx, ·⟩)
    · rintro (rfl | ⟨hx, -⟩ | ⟨hx, -⟩)
      exacts [huv, hx, hx]
  rw [← h.card_outNbrs u, hsplit, card_insert_of_notMem (by simp [h.arc_self]),
    card_union_of_disjoint hdisj, h.card_commonOut (h.ne_of_arc huv)]
end BSLambda.IsDRTournamentWith
