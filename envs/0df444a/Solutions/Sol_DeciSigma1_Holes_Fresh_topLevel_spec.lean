-- Prove2me | solution 1 for DeciSigma1.Holes.Fresh.topLevel_spec
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T13:45:32.631821+00:00
-- url     : https://prove2.me/submissions/c24cabe2-f109-4c56-9fd4-14bc15e4b3a1

module
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Definitions.Def_LeanPool_DeciSigma1_Readers_Basic
public import Mathlib.Order.Nat
public import Mathlib.Algebra.Group.Action.Defs
public import Mathlib.Order.Interval.Finset.Nat
public import Definitions.Def_LeanPool_DeciSigma1_Holes_Fresh_Hierarchy
public import Theorems.Thm_DeciSigma1_Holes_Fresh_active_eq_empty_of_totalLength_lt

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
theorem _root_.solution :
    active W (topLevel W + 1) = ∅ ∧ ∀ t < topLevel W, active W (t + 1) ≠ ∅ := by
  refine ⟨?_, fun t ht h => ?_⟩
  · rcases Nat.find_spec
      (⟨totalLength W, Or.inr le_rfl⟩ : ∃ t, active W (t + 1) = ∅ ∨ totalLength W ≤ t)
      with h | h
    · exact h
    · exact active_eq_empty_of_totalLength_lt (by unfold topLevel; omega)
  · exact Nat.find_min _ ht (Or.inl h)
end DeciSigma1.Holes.Fresh
