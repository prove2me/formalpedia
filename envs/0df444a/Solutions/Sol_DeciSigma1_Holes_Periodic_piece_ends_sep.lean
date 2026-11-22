-- Prove2me | solution 1 for DeciSigma1.Holes.Periodic.piece_ends_sep
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T13:48:50.379801+00:00
-- url     : https://prove2.me/submissions/0d2a1745-9991-4bef-b180-eb03af7e36f1

module
public import Definitions.Def_LeanPool_DeciSigma1_Readers_Basic
public import Definitions.Def_LeanPool_DeciSigma1_Words_Periods
public import Mathlib.Order.Nat
public import Definitions.Def_LeanPool_DeciSigma1_Holes_Periodic_Basic
public import Theorems.Thm_DeciSigma1_Holes_Periodic_FollowerEdge_symm
public import Theorems.Thm_DeciSigma1_Holes_Periodic_Piece_sep
public import Theorems.Thm_DeciSigma1_Words_IsConjugate_symm


set_option autoImplicit true
@[expose] public section
public section
open DeciSigma1 DeciSigma1.Holes DeciSigma1.Holes.Periodic
open DeciSigma1.Readers DeciSigma1.Words
variable {α : Type} {k : ℕ}
variable {W : Fin k → List α} {d : ℕ}
namespace DeciSigma1.Holes.Periodic
theorem _root_.solution {P Q : Piece W d} (hne : P ≠ Q) (hl : P.coordinate = Q.coordinate) :
    d < (P.stop : ℤ) - Q.stop ∨ d < (Q.stop : ℤ) - P.stop := by
  rcases le_total P.start Q.start with h | h
  · have := Piece.sep hne hl h; right; omega
  · have := Piece.sep (Ne.symm hne) hl.symm h; left; omega
end DeciSigma1.Holes.Periodic
