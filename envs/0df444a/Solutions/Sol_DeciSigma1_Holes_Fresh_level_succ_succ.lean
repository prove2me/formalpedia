-- Prove2me | solution 1 for DeciSigma1.Holes.Fresh.level_succ_succ
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T13:16:50.407999+00:00
-- url     : https://prove2.me/submissions/1e5f055f-1736-4b65-b55f-1d4bc7f8ab7f

module
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Definitions.Def_LeanPool_DeciSigma1_Readers_Basic
public import Mathlib.Order.Nat
public import Mathlib.Algebra.Group.Action.Defs
public import Mathlib.Order.Interval.Finset.Nat
public import Definitions.Def_LeanPool_DeciSigma1_Holes_Fresh_Hierarchy

set_option autoImplicit true
@[expose] public section
public section
open DeciSigma1 DeciSigma1.Holes DeciSigma1.Holes.Fresh
open DeciSigma1.Readers
open Finset
variable {α : Type} {k : ℕ}
variable [DecidableEq α]
variable (W : Fin k → List α)
namespace DeciSigma1.Holes.Fresh
theorem _root_.solution (t : ℕ) : level W (t + 2) = (level W (t + 1)).next W := rfl
end DeciSigma1.Holes.Fresh
