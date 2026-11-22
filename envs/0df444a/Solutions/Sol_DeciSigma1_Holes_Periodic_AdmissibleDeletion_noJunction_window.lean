-- Prove2me | solution 1 for DeciSigma1.Holes.Periodic.AdmissibleDeletion.noJunction_window
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T14:46:55.380286+00:00
-- url     : https://prove2.me/submissions/ac020912-a980-4864-aed2-406abf5e38c1

module
public import Mathlib.Tactic.Positivity.Basic
public import Definitions.Def_LeanPool_DeciSigma1_Holes_Periodic_Pieces
public import Definitions.Def_LeanPool_DeciSigma1_Holes_Periodic_Transport

set_option autoImplicit true
@[expose] public section
public section
open DeciSigma1 DeciSigma1.Holes DeciSigma1.Holes.Periodic
open DeciSigma1.Readers DeciSigma1.Words
open DeciSigma1.Readers.Table
variable {α : Type} {k : ℕ}
open DeciSigma1.Holes.Periodic.AdmissibleDeletion
variable [DecidableEq α] {W : Fin k → List α} {ρ : List α} {N : ℕ} {x : Piece W ρ.length → ℕ}
variable (hx : AdmissibleDeletion W ρ N x)
include hx
namespace DeciSigma1.Holes.Periodic.AdmissibleDeletion
theorem _root_.solution {l : Fin k} {c' m n : ℕ} (hNJ : hx.NoInteriorJunction l c' m)
    (hn : n ≤ m)
    (hafter : ∀ R : Piece W ρ.length, R.coordinate = l → x R ≠ 0 → c' < (hx.imagePiece R).start →
      (hx.imagePiece R).start + Periodic.boundaryMargin N ρ.length < c' + n → False) :
    ∀ R : Piece W ρ.length, R.coordinate = l → x R ≠ 0 →
      ¬ (c' < (hx.imagePiece R).start + Periodic.boundaryMargin N ρ.length ∧
        (hx.imagePiece R).start + Periodic.boundaryMargin N ρ.length < c' + n) := by
  rintro R hRl hxR ⟨h1, h2⟩
  by_cases hs : (hx.imagePiece R).start ≤ c'
  · have := hNJ R hRl hxR hs h1; omega
  · exact hafter R hRl hxR (by omega) h2
end DeciSigma1.Holes.Periodic.AdmissibleDeletion
