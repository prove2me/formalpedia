-- Prove2me | solution 1 for Erdos684.log_smallPrimePart
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T15:39:54.150383+00:00
-- url     : https://prove2.me/submissions/b559e330-07a7-46a1-bb89-8dbfffc176f6

module
public import Mathlib.Data.Nat.Choose.Factorization
public import Mathlib.NumberTheory.PrimeCounting
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Lean.Elab.Tactic.Omega
public import Definitions.Def_Erdos684_Finite

set_option autoImplicit false
@[expose] public section
public section
open Erdos684
namespace Erdos684
theorem _root_.solution (n k : ℕ) :
    Real.log (smallPrimePart n k : ℝ) =
      ∑ p ∈ Nat.primesLE k, ((n.choose k).factorization p : ℝ) * Real.log p := by
  rw [smallPrimePart, Nat.cast_prod, Real.log_prod]
  · apply Finset.sum_congr rfl
    intro p _
    rw [Nat.cast_pow, Real.log_pow]
  · intro p hp
    exact_mod_cast pow_ne_zero ((n.choose k).factorization p) (Nat.prime_of_mem_primesLE hp).ne_zero
end Erdos684
