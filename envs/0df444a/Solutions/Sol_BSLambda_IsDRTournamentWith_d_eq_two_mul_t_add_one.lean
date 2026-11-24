-- Prove2me | solution 1 for BSLambda.IsDRTournamentWith.d_eq_two_mul_t_add_one
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T00:56:42.738978+00:00
-- url     : https://prove2.me/submissions/6f347f09-08f2-4ed9-895d-a6b019d350a6

module
public import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
public import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
public import Mathlib.Data.Fintype.Card
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_Defs_Tournament
public import Theorems.Thm_BSLambda_IsTournament_ne_of_arc
public import Theorems.Thm_BSLambda_mem_outNbrs
public import Theorems.Thm_BSLambda_sum_card_commonOut_eq_sum_card_middles
public import Theorems.Thm_BSLambda_IsDRTournamentWith_card_middles_add_add_one
public import Theorems.Thm_BSLambda_IsDRTournamentWith_d_pos
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
theorem _root_.solution [Nontrivial ι] : d = 2 * t + 1 := by
  obtain ⟨x⟩ : Nonempty ι := inferInstance
  obtain ⟨w, hw⟩ : (outNbrs Arc x).Nonempty := by
    rw [← card_pos, h.card_outNbrs x]
    exact h.d_pos
  have hall (y : ι) (hy : y ∈ outNbrs Arc x) :
      (middles Arc x y).card = (middles Arc x w).card := by
    have h1 := h.card_middles_add_add_one (mem_outNbrs.1 hy)
    have h2 := h.card_middles_add_add_one (mem_outNbrs.1 hw)
    omega
  have hL : ∑ y ∈ outNbrs Arc x, (commonOut Arc x y).card = d * t := by
    rw [sum_const_nat fun y hy ↦ h.card_commonOut (h.ne_of_arc (mem_outNbrs.1 hy)),
      h.card_outNbrs x]
  have hR : ∑ y ∈ outNbrs Arc x, (middles Arc x y).card = d * (middles Arc x w).card := by
    rw [sum_const_nat hall, h.card_outNbrs x]
  have hm := h.card_middles_add_add_one (mem_outNbrs.1 hw)
  have := Nat.eq_of_mul_eq_mul_left h.d_pos
    (hL.symm.trans ((sum_card_commonOut_eq_sum_card_middles Arc x).trans hR))
  omega
end BSLambda.IsDRTournamentWith
