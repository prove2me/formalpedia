-- Prove2me | solution 1 for DeciSigma1.Holes.Periodic.Piece.sep
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T12:56:09.100018+00:00
-- url     : https://prove2.me/submissions/b24f423d-df54-4c01-8e7b-aa58c89c14a1

module
public import Definitions.Def_LeanPool_DeciSigma1_Readers_Basic
public import Definitions.Def_LeanPool_DeciSigma1_Words_Periods
public import Mathlib.Order.Nat
public import Definitions.Def_LeanPool_DeciSigma1_Holes_Periodic_Basic
public import Theorems.Thm_DeciSigma1_Holes_Periodic_Piece_period_pos
public import Theorems.Thm_DeciSigma1_Holes_Periodic_piece_eq_of_overlap

set_option autoImplicit true
@[expose] public section
public section
open DeciSigma1 DeciSigma1.Holes DeciSigma1.Holes.Periodic
open DeciSigma1.Readers DeciSigma1.Words
variable {α : Type} {k : ℕ}
variable {W : Fin k → List α} {d : ℕ}
namespace DeciSigma1.Holes.Periodic
namespace Piece
theorem _root_.solution {P Q : Piece W d} (hne : P ≠ Q) (hl : P.coordinate = Q.coordinate)
    (hs : P.start ≤ Q.start) :
    P.start < Q.start ∧ P.stop < Q.start + d ∧ P.stop + d < Q.stop := by
  have hP := P.long; have hQ := Q.long; have hd := P.period_pos
  have h1 : ¬ (P.start + d ≤ Q.stop ∧ Q.start + d ≤ P.stop) :=
      fun h => hne (piece_eq_of_overlap hl h.1 h.2)
  have h2 : P.stop < Q.start + d := by
    by_contra h; exact h1 ⟨by omega, by omega⟩
  exact ⟨by omega, h2, by omega⟩
end Piece
end DeciSigma1.Holes.Periodic
