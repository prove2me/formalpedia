-- Prove2me | solution 1 for DeciSigma1.Holes.Periodic.AdmissibleDeletion.keepCut_of_mem
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T14:48:23.870637+00:00
-- url     : https://prove2.me/submissions/7370fa47-befc-4ef7-bf06-7b9613fbd978

module
public import Definitions.Def_LeanPool_DeciSigma1_Arithmetic_FinitePaths
public import Definitions.Def_LeanPool_DeciSigma1_Holes_Periodic_Deletion
public import Mathlib.Data.Nat.ModEq
public import Mathlib.Tactic.Ring.RingNF
public import Definitions.Def_LeanPool_DeciSigma1_Holes_Periodic_Pieces
public import Theorems.Thm_DeciSigma1_Holes_Periodic_AdmissibleDeletion_retainedCount_junction
public import Theorems.Thm_DeciSigma1_Holes_Periodic_mem_deletedPositions
public import Theorems.Thm_DeciSigma1_Words_retainedCount_add_of_mem


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
theorem _root_.solution {l : Fin k} {p : ℕ} (hp : p ∈ deletedPositions W ρ N x l) :
    ∃ R : Piece W ρ.length, R.coordinate = l ∧ x R ≠ 0 ∧
      retainedCount (deletedPositions W ρ N x l) p =
        (hx.imagePiece R).start + Periodic.boundaryMargin N ρ.length := by
  obtain ⟨R, _, hRl, h1, h2⟩ := mem_deletedPositions.mp hp
  have hxR : x R ≠ 0 := by intro h0; rw [h0] at h2; omega
  subst hRl
  refine ⟨R, rfl, hxR, ?_⟩
  rw [← hx.retainedCount_junction R hxR]
  obtain ⟨n, rfl⟩ := Nat.exists_eq_add_of_le h1
  exact retainedCount_add_of_mem fun i hi => hx.site_sub (by omega) (by omega)
end DeciSigma1.Holes.Periodic.AdmissibleDeletion
