-- Prove2me | solution 1 for DeciSigma1.Holes.Periodic.Piece.periodicOn
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T12:47:11.79885+00:00
-- url     : https://prove2.me/submissions/316b8d03-2880-46c5-81d0-db3401af31b6

module
public import Definitions.Def_LeanPool_DeciSigma1_Readers_Basic
public import Definitions.Def_LeanPool_DeciSigma1_Words_Periods
public import Mathlib.Order.Nat
public import Definitions.Def_LeanPool_DeciSigma1_Holes_Periodic_Basic

set_option autoImplicit true
@[expose] public section
public section
open DeciSigma1 DeciSigma1.Holes DeciSigma1.Holes.Periodic
open DeciSigma1.Readers DeciSigma1.Words
variable {α : Type} {k : ℕ}
open DeciSigma1.Holes.Periodic.Piece
variable {W : Fin k → List α} {d : ℕ}
namespace DeciSigma1.Holes.Periodic.Piece
theorem _root_.solution (P : Piece W d) : PeriodicOn (W P.coordinate) d P.start P.stop := P.periodic
end DeciSigma1.Holes.Periodic.Piece
