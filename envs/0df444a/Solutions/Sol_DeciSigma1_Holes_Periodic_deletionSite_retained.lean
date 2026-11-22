-- Prove2me | solution 1 for DeciSigma1.Holes.Periodic.deletionSite_retained
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T14:49:51.102318+00:00
-- url     : https://prove2.me/submissions/10d18501-99ac-4f3f-81ea-654d3146385b

module
public import Mathlib.Tactic.Positivity.Basic
public import Definitions.Def_LeanPool_DeciSigma1_Holes_Periodic_Pieces
public import Definitions.Def_LeanPool_DeciSigma1_Holes_Periodic_Transport
public import Theorems.Thm_DeciSigma1_Holes_Periodic_AdmissibleDeletion_site_bound
public import Theorems.Thm_DeciSigma1_Holes_Periodic_FollowerEdge_symm
public import Theorems.Thm_DeciSigma1_Holes_Periodic_Piece_period_pos
public import Theorems.Thm_DeciSigma1_Holes_Periodic_fw_overlap
public import Theorems.Thm_DeciSigma1_Holes_Periodic_mem_deletedPositions
public import Theorems.Thm_DeciSigma1_Holes_Periodic_mem_piecesOf
public import Theorems.Thm_DeciSigma1_Holes_Periodic_two_d_le_boundaryMargin
public import Theorems.Thm_DeciSigma1_Readers_Dominates_trans
public import Theorems.Thm_DeciSigma1_Readers_FreshDominates_trans
public import Theorems.Thm_DeciSigma1_Words_IsConjugate_symm
public import Theorems.Thm_DeciSigma1_Words_IsConjugate_trans


set_option autoImplicit true
@[expose] public section
public section
open DeciSigma1 DeciSigma1.Holes DeciSigma1.Holes.Periodic
open DeciSigma1.Readers DeciSigma1.Words
open DeciSigma1.Readers.Table
variable {α : Type} {k : ℕ}
variable [DecidableEq α] {S : Type} [Fintype S] [DecidableEq S] {W : Fin k → List α}
  {ρ : List α} {x : Piece W ρ.length → ℕ}
variable {N dR : ℕ} (hx : AdmissibleDeletion W ρ N x)
include hx
namespace DeciSigma1.Holes.Periodic
theorem _root_.solution (hN : 0 < N) (R : Piece W dR)
    (hcls : ¬ IsConjugate R.root ρ) (hd : dR ≤ ρ.length)
    (hlen : ρ.length + dR ≤ R.len) {p : ℕ}
    (hp : R.start ≤ p + 1) (hpe : p ≤ R.stop) : p ∉ deletedPositions W ρ N x R.coordinate := by
  intro hdel
  obtain ⟨P, hP, hl, hstart, hend⟩ := mem_deletedPositions.mp hdel
  have hmove : x P ≠ 0 := by intro hz; rw [hz] at hend; omega
  have hb := hx.site_bound hmove
  have hA := Periodic.two_d_le_boundaryMargin hN ρ.length
  have hdp := P.period_pos
  have hdiff : ¬ IsConjugate P.root R.root := by
    intro hc
    exact hcls (hc.symm.trans ((mem_piecesOf W).mp hP))
  have hf := fw_overlap P R hdiff hd hl
  unfold Piece.len at hlen
  omega
end DeciSigma1.Holes.Periodic
