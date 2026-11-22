-- Prove2me | solution 1 for DeciSigma1.Holes.Tail.PeriodicCover.mono
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T14:54:13.684718+00:00
-- url     : https://prove2.me/submissions/c5c57141-0127-49c3-a7b8-3b48b76e1a65

module
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Definitions.Def_LeanPool_DeciSigma1_Holes_Periodic_Basic
public import Definitions.Def_LeanPool_DeciSigma1_Holes_Tail_ClosedFactors
public import Mathlib.Order.Nat
public import Mathlib.Data.Nat.ModEq
public import Mathlib.Algebra.Group.Action.Defs
public import Mathlib.Data.Fintype.Pigeonhole
public import Mathlib.Data.Fintype.Sum
public import Mathlib.Tactic.Ring.RingNF
public import Mathlib.Algebra.GroupWithZero.Nat
public import Definitions.Def_LeanPool_DeciSigma1_Holes_Tail_Levels
public import Theorems.Thm_DeciSigma1_Readers_Dominates_trans
public import Theorems.Thm_DeciSigma1_Readers_FreshDominates_trans
public import Theorems.Thm_DeciSigma1_Words_IsConjugate_trans


set_option autoImplicit true
@[expose] public section
public section
open DeciSigma1 DeciSigma1.Holes DeciSigma1.Holes.Tail
open DeciSigma1.Holes.Periodic DeciSigma1.Readers DeciSigma1.Words
variable {α S : Type} {k : ℕ}
namespace DeciSigma1.Holes.Tail
namespace PeriodicCover
theorem _root_.solution {w : List α} {J P E T P' E' T' : ℕ} (h : PeriodicCover w J P E T)
    (hP : P ≤ P')
    (hE : E ≤ E') (hT : T ≤ T') : PeriodicCover w J P' E' T' := by
  obtain ⟨fs, h1, h2, h3⟩ := h
  exact ⟨fs, h1.trans hP, fun f hf => let ⟨a, b, c, d⟩ := h2 f hf; ⟨a, b.trans hE, c, d⟩,
    h3.trans hT⟩
end PeriodicCover
end DeciSigma1.Holes.Tail
