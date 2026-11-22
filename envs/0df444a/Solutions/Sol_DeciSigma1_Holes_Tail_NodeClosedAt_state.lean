-- Prove2me | solution 1 for DeciSigma1.Holes.Tail.NodeClosedAt.state
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T14:50:38.127308+00:00
-- url     : https://prove2.me/submissions/ff629dbf-26ca-4a1a-adaf-aa3a114ebabd

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
public import Theorems.Thm_DeciSigma1_Holes_Tail_runFrom_eq_suffixNode

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
namespace NodeClosedAt
theorem _root_.solution (hcl : NodeClosedAt T q0 D x c c') :
    runFrom T.step q0 (x.take c) = runFrom T.step q0 (x.take c') := by
  rw [runFrom_eq_suffixNode T q0 D (x.take c), runFrom_eq_suffixNode T q0 D (x.take c'),
    hcl.2.2]
end NodeClosedAt
end DeciSigma1.Holes.Tail
