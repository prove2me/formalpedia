-- Prove2me | solution 1 for DeciSigma1.Holes.Fresh.anchorCount_self
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T12:53:14.138085+00:00
-- url     : https://prove2.me/submissions/43f71d25-055e-4aa2-a49b-11a808897367

module
public import Definitions.Def_LeanPool_DeciSigma1_Holes_Fresh_Hierarchy
public import Mathlib.Order.Nat
public import Mathlib.Algebra.GroupWithZero.Nat
public import Definitions.Def_LeanPool_DeciSigma1_Holes_Fresh_Parsing

set_option autoImplicit true
@[expose] public section
public section
open DeciSigma1 DeciSigma1.Holes DeciSigma1.Holes.Fresh
open Finset
variable {A : Finset ℕ}
namespace DeciSigma1.Holes.Fresh
theorem _root_.solution (s : ℕ) : anchorCount A s s = 0 := by
  unfold anchorCount
  rw [card_eq_zero, filter_eq_empty_iff]
  intro q _; omega
end DeciSigma1.Holes.Fresh
