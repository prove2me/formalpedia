-- Prove2me | solution 1 for DeciSigma1.Holes.Periodic.FollowerEdge.symm
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T12:44:28.775369+00:00
-- url     : https://prove2.me/submissions/8b876369-5784-49d2-a0a4-db8171aba3db

module
public import Definitions.Def_LeanPool_DeciSigma1_Readers_Basic
public import Definitions.Def_LeanPool_DeciSigma1_Words_Periods
public import Mathlib.Order.Nat
public import Definitions.Def_LeanPool_DeciSigma1_Holes_Periodic_Basic
public import Theorems.Thm_DeciSigma1_Words_IsConjugate_symm


set_option autoImplicit true
@[expose] public section
public section
open DeciSigma1 DeciSigma1.Holes DeciSigma1.Holes.Periodic
open DeciSigma1.Readers DeciSigma1.Words
variable {α : Type} {k : ℕ}
namespace DeciSigma1.Holes.Periodic
namespace FollowerEdge
theorem _root_.solution {W : Fin k → List α} {d : ℕ} {P Q : Piece W d} (h : FollowerEdge P Q) :
    FollowerEdge Q P :=
  Or.symm h
end FollowerEdge
end DeciSigma1.Holes.Periodic
