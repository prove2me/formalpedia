-- Prove2me | solution 1 for DeciSigma1.Holes.Tail.length_pow_loop
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T14:51:03.174083+00:00
-- url     : https://prove2.me/submissions/b2c7a7c2-5055-427d-a48b-c7e78a4239dc

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
theorem _root_.solution (hc' : c' ≤ x.length) (n : ℕ) :
    (pow ((x.drop c).take (c' - c)) n).length = n * (c' - c) := by
  rw [Words.length_pow, length_loop hc']
end DeciSigma1.Holes.Tail
