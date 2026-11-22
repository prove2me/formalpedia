-- Prove2me | solution 1 for DeciSigma1.Holes.Periodic.exists_preserved_piece_of_nonconjugate_root
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T14:50:47.528364+00:00
-- url     : https://prove2.me/submissions/ed14d4af-4ffb-4cfe-a0c1-5a429b1e7aff

module
public import Mathlib.Tactic.Positivity.Basic
public import Definitions.Def_LeanPool_DeciSigma1_Holes_Periodic_Pieces
public import Definitions.Def_LeanPool_DeciSigma1_Holes_Periodic_Transport
public import Theorems.Thm_DeciSigma1_Holes_Periodic_deletionSite_retained
public import Theorems.Thm_DeciSigma1_Holes_Periodic_Piece_start_lt_stop
public import Theorems.Thm_DeciSigma1_Holes_Periodic_isPeriodicPiece_deletePositions_with_root


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
    (hlen : ρ.length + dR ≤ R.len) :
    (∀ p, R.start ≤ p → p < R.stop → p ∉ deletedPositions W ρ N x R.coordinate) ∧
    (R.start ≠ 0 → R.start - 1 ∉ deletedPositions W ρ N x R.coordinate) ∧
    (R.stop < (W R.coordinate).length → R.stop ∉ deletedPositions W ρ N x R.coordinate) ∧
    ∃ R' : Piece (editedTuple W ρ N x) dR,
      R'.coordinate = R.coordinate ∧ R'.len = R.len ∧ R'.root = R.root := by
  have hret : ∀ {p}, R.start ≤ p + 1 → p ≤ R.stop → p ∉ deletedPositions W ρ N x R.coordinate :=
    by intro p; exact deletionSite_retained hx hN R hcls hd hlen (p := p)
  have hin : ∀ p, R.start ≤ p → p < R.stop → p ∉ deletedPositions W ρ N x R.coordinate :=
    fun p hp he => hret (by omega) (by omega)
  have hleft : R.start ≠ 0 → R.start - 1 ∉ deletedPositions W ρ N x R.coordinate :=
    fun hs => hret (by omega) (by have := R.start_lt_stop; omega)
  have hright : R.stop ∉ deletedPositions W ρ N x R.coordinate :=
    hret (by have := R.start_lt_stop; omega) le_rfl
  refine ⟨hin, hleft, fun _ => hright, ?_⟩
  obtain ⟨hpiece, hlength, hroot⟩ :=
    isPeriodicPiece_deletePositions_with_root (U' := editedTuple W ρ N x) rfl
      R.isPeriodicPiece hin hleft (fun _ => hright)
  refine ⟨Piece.ofIsPeriodicPiece hpiece, rfl, ?_, ?_⟩
  · change retainedCount (deletedPositions W ρ N x R.coordinate) R.stop -
      retainedCount (deletedPositions W ρ N x R.coordinate) R.start = R.stop - R.start
    omega
  · exact hroot
end DeciSigma1.Holes.Periodic
