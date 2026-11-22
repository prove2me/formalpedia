-- Prove2me | solution 1 for DeciSigma1.Holes.Periodic.Piece.window_isConjugate
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T12:58:28.833794+00:00
-- url     : https://prove2.me/submissions/7d9d74f5-5ac5-421a-a1e5-cafcb350b48b

module
public import Definitions.Def_LeanPool_DeciSigma1_Readers_Basic
public import Definitions.Def_LeanPool_DeciSigma1_Words_Periods
public import Mathlib.Order.Nat
public import Definitions.Def_LeanPool_DeciSigma1_Holes_Periodic_Basic
public import Theorems.Thm_DeciSigma1_Holes_Periodic_Piece_periodicOn
public import Theorems.Thm_DeciSigma1_Words_PeriodicOn_window_rotate


set_option autoImplicit true
@[expose] public section
public section
open DeciSigma1 DeciSigma1.Holes DeciSigma1.Holes.Periodic
open DeciSigma1.Readers DeciSigma1.Words
variable {α : Type} {k : ℕ}
open DeciSigma1.Holes.Periodic.Piece
variable {W : Fin k → List α} {d : ℕ}
namespace DeciSigma1.Holes.Periodic.Piece
theorem _root_.solution (P : Piece W d) {z : ℕ} (hz : P.start ≤ z) (hze : z + d ≤ P.stop) :
    IsConjugate P.root (((W P.coordinate).drop z).take d) :=
  ⟨_, P.periodicOn.window_rotate P.stop_le_length hz hze⟩
end DeciSigma1.Holes.Periodic.Piece
