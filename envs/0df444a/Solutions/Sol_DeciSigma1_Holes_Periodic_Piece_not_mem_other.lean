-- Prove2me | solution 1 for DeciSigma1.Holes.Periodic.Piece.not_mem_other
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T13:48:58.13678+00:00
-- url     : https://prove2.me/submissions/3b0a9b59-96bc-4b1e-82b0-8099f692b3a5

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
namespace Piece
theorem _root_.solution {P Q : Piece W d} (hne : P ≠ Q) (hl : P.coordinate = Q.coordinate)
    {p : ℕ}
    (hp1 : P.start + d ≤ p) (hp2 : p + d < P.stop) : ¬ (Q.start ≤ p ∧ p < Q.stop) := by
  rintro ⟨hq1, hq2⟩
  rcases le_total P.start Q.start with h | h
  · have := Piece.sep hne hl h; omega
  · have := Piece.sep (Ne.symm hne) hl.symm h; omega
end Piece
end DeciSigma1.Holes.Periodic
