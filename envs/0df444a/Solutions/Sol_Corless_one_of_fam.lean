-- Prove2me | solution 1 for Corless.one_of_fam
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-20T22:49:03.688334+00:00
-- url     : https://prove2.me/submissions/4c1f8d50-7868-4715-894b-164d1e54ba2f

module
public import Mathlib.Algebra.BigOperators.Intervals
public import Definitions.Def_LeanPool_CorlessNilpotent_Parity
public import Definitions.Def_LeanPool_CorlessNilpotent_Main
public import Theorems.Thm_Corless_fold_eq
public import Theorems.Thm_Corless_Dv_one
public import Theorems.Thm_Corless_Dv_zero
attribute [local simp] Corless.Dv_one
attribute [local simp] Corless.Dv_zero



set_option autoImplicit true
@[expose] public section
public section
open Polynomial Finset
open Corless
namespace Corless
theorem _root_.solution {s : ℕ → ℤ} : ∀ k, Fam k s → Dv s (2 ^ (k + 1) - 1) = 1
  | 0, _ => by simp
  | k + 1, ⟨folded, hk⟩ => by
      rw [fold_eq folded, solution k hk, one_pow]
end Corless
