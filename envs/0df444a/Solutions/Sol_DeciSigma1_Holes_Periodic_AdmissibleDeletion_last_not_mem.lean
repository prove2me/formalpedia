-- Prove2me | solution 1 for DeciSigma1.Holes.Periodic.AdmissibleDeletion.last_not_mem
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T14:48:39.56964+00:00
-- url     : https://prove2.me/submissions/fbcc2f58-0cbe-4de0-bdde-240bd0a42246

module
public import Definitions.Def_LeanPool_DeciSigma1_Arithmetic_FinitePaths
public import Definitions.Def_LeanPool_DeciSigma1_Holes_Periodic_Deletion
public import Mathlib.Data.Nat.ModEq
public import Mathlib.Tactic.Ring.RingNF
public import Definitions.Def_LeanPool_DeciSigma1_Holes_Periodic_Pieces
public import Theorems.Thm_DeciSigma1_Holes_Periodic_AdmissibleDeletion_site_bound
public import Theorems.Thm_DeciSigma1_Holes_Periodic_Piece_period_pos
public import Theorems.Thm_DeciSigma1_Holes_Periodic_d_le_boundaryMargin
public import Theorems.Thm_DeciSigma1_Holes_Periodic_mem_deletedPositions


set_option autoImplicit true
@[expose] public section
public section
open DeciSigma1 DeciSigma1.Holes DeciSigma1.Holes.Periodic
open DeciSigma1.Readers DeciSigma1.Words
open DeciSigma1.Readers.Table
variable {α S : Type} [DecidableEq α] {k : ℕ} {W : Fin k → List α} {ρ : List α}
open DeciSigma1.Holes.Periodic.AdmissibleDeletion
variable {N : ℕ} {x : Piece W ρ.length → ℕ} (hx : AdmissibleDeletion W ρ N x)
include hx
namespace DeciSigma1.Holes.Periodic.AdmissibleDeletion
theorem _root_.solution (l : Fin k) (h : 0 < (W l).length) :
    (W l).length - 1 ∉ deletedPositions W ρ N x l := by
  intro hm
  obtain ⟨R, _, hRl, h1, h2⟩ := mem_deletedPositions.mp hm
  have hxR : x R ≠ 0 := by intro h0; rw [h0] at h2; omega
  have hb := hx.site_bound hxR
  have := R.stop_le_length; have := R.period_pos; have := Periodic.d_le_boundaryMargin N ρ.length
  subst hRl; omega
end DeciSigma1.Holes.Periodic.AdmissibleDeletion
