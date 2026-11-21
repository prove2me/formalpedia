-- Prove2me | solution 1 for Corless.fold_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-20T22:43:55.458583+00:00
-- url     : https://prove2.me/submissions/84de304b-a3e8-4222-bc89-9ade6e5d577b

module
public import Mathlib.Algebra.BigOperators.Intervals
public import Definitions.Def_LeanPool_CorlessNilpotent_Parity
public import Definitions.Def_LeanPool_CorlessNilpotent_Main
public import Theorems.Thm_Corless_Dv_fold
public import Theorems.Thm_Corless_folded_sizes


set_option autoImplicit true
@[expose] public section
public section
open Polynomial Finset
open Corless
namespace Corless
theorem _root_.solution {k : ℕ} {s : ℕ → ℤ} (h : IsFolded s (2 ^ (k + 1) - 2)) :
    Dv s (2 ^ (k + 2) - 1) = Dv s (2 ^ (k + 1) - 1) ^ 2 := by
  obtain ⟨half, full⟩ := folded_sizes k
  rw [full, half]
  exact Dv_fold s _ h
end Corless
