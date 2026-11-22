-- Prove2me | solution 1 for DeciSigma1.Holes.Tail.factorLengthBound_mono
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T13:09:00.262806+00:00
-- url     : https://prove2.me/submissions/a74c6d57-1d11-437d-8d2d-0e330a58d59c

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
variable [DecidableEq α] {D : Finset (List α)}
variable {T : Table α S k} {q0 : S} {x : List α} {B c c' : ℕ}
namespace DeciSigma1.Holes.Tail
theorem _root_.solution (m N : ℕ) : Monotone (factorLengthBound m N) := by
  intro B B' h
  have h1 : B * (B + 1) / 2 ≤ B' * (B' + 1) / 2 :=
    Nat.div_le_div_right (Nat.mul_le_mul h (by omega))
  exact Nat.mul_le_mul (by omega)
    (Nat.mul_le_mul_left _ (Nat.add_le_add_right (Nat.mul_le_mul_left _ h1) 1))
end DeciSigma1.Holes.Tail
