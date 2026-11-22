-- Prove2me | solution 1 for DeciSigma1.Holes.Tail.take_append_suffix
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T12:56:20.635041+00:00
-- url     : https://prove2.me/submissions/e6076692-2f92-4c77-96c1-5195e74860d1

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
namespace DeciSigma1.Holes.Tail
theorem _root_.solution {s w : List α} (h : s <:+ w) :
    w.take (w.length - s.length) ++ s = w := by
  conv_rhs => rw [← List.take_append_drop (w.length - s.length) w]
  rw [← List.suffix_iff_eq_drop.mp h]
end DeciSigma1.Holes.Tail
