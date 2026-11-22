-- Prove2me | solution 1 for DeciSigma1.Holes.Tail.le_length_pow_loop
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T14:51:48.971983+00:00
-- url     : https://prove2.me/submissions/1310195d-3468-415b-a012-b2bc549cca3a

module
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Definitions.Def_LeanPool_DeciSigma1_Arithmetic_DifferenceConstraints
public import Definitions.Def_LeanPool_DeciSigma1_Words_Basic
public import Definitions.Def_LeanPool_DeciSigma1_Words_SuffixChains
public import Mathlib.Order.Nat
public import Mathlib.Data.Nat.ModEq
public import Mathlib.Algebra.Group.Action.Defs
public import Mathlib.Data.Fintype.Pigeonhole
public import Mathlib.Tactic.Ring.RingNF
public import Definitions.Def_LeanPool_DeciSigma1_Holes_Tail_Rays
public import Theorems.Thm_DeciSigma1_Holes_Tail_length_pow_loop

set_option autoImplicit true
@[expose] public section
public section
open DeciSigma1 DeciSigma1.Holes DeciSigma1.Holes.Tail
open DeciSigma1.Readers
open DeciSigma1.Words (pow)
open DeciSigma1.Readers.Table
variable {α S : Type} {k : ℕ}
variable {x : List α} {c c' L : ℕ}
namespace DeciSigma1.Holes.Tail
theorem _root_.solution (hcc : c < c') (hc' : c' ≤ x.length) (L : ℕ) :
    L + 1 ≤ (pow ((x.drop c).take (c' - c)) (L + 1)).length := by
  rw [length_pow_loop hc']; exact Nat.le_mul_of_pos_right _ (by omega)
end DeciSigma1.Holes.Tail
