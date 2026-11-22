-- Prove2me | solution 1 for DeciSigma1.Holes.Fresh.marker_suffix
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T12:45:09.806281+00:00
-- url     : https://prove2.me/submissions/939c93f6-dac8-45b5-aed6-a7e16423dc9e

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
theorem _root_.solution (t : ℕ) (l : Fin k) : marker W t l <:+ W l := by
  rcases t with _ | _ | t
  · exact List.nil_suffix
  · exact List.drop_suffix _ _
  · exact List.drop_suffix _ _
end DeciSigma1.Holes.Fresh
