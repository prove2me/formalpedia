-- Prove2me | solution 1 for DeciSigma1.Holes.Fresh.marker_eq_of_infix
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T13:36:59.477807+00:00
-- url     : https://prove2.me/submissions/efee7f71-e72f-40aa-a4b6-de36fc8df11e

module
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Definitions.Def_LeanPool_DeciSigma1_Readers_Basic
public import Mathlib.Order.Nat
public import Mathlib.Algebra.Group.Action.Defs
public import Mathlib.Order.Interval.Finset.Nat
public import Definitions.Def_LeanPool_DeciSigma1_Holes_Fresh_Hierarchy
public import Theorems.Thm_DeciSigma1_Holes_Fresh_level_anti

set_option autoImplicit true
@[expose] public section
public section
open DeciSigma1 DeciSigma1.Holes DeciSigma1.Holes.Fresh
open DeciSigma1.Readers
open Finset
variable {α : Type} {k : ℕ}
variable [DecidableEq α]
variable {W : Fin k → List α}
namespace DeciSigma1.Holes.Fresh
theorem _root_.solution (t : ℕ) (m m' : Fin k) (hm : m ∈ active W t)
    (hm' : m' ∈ active W t) : marker W t m <:+: marker W t m' → marker W t m = marker W t m' := by
  rcases t with _ | t
  · intro _; rfl
  · exact (level_anti t).2 m hm m' hm'
end DeciSigma1.Holes.Fresh
