-- Prove2me | solution 1 for Corless.f_pow_two
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-20T22:44:30.659196+00:00
-- url     : https://prove2.me/submissions/e9f27dc9-6299-4250-8e1f-2d047525de1f

module
public import Mathlib.Algebra.CharP.Lemmas
public import Mathlib.Algebra.CharP.Reduced
public import Mathlib.Algebra.Field.ZMod
public import Mathlib.Algebra.Polynomial.Eval.Coeff
public import Mathlib.Tactic.LinearCombination
public import Definitions.Def_LeanPool_CorlessNilpotent_Path
public import Definitions.Def_LeanPool_CorlessNilpotent_Parity
public import Theorems.Thm_Corless_Dv_parity
public import Theorems.Thm_Corless_folded_sizes
public import Theorems.Thm_Corless_isSign_star
public import Theorems.Thm_Corless_Dv_star
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
theorem _root_.solution (k : ℕ) : ∃ A : ℤ[X], f (2 ^ (k + 1) - 1) = 1 + 2 * A := by
  induction k with
  | zero => exact ⟨0, by simp [f]⟩
  | succ k ih =>
      obtain ⟨A, hA⟩ := ih
      let n := 2 ^ (k + 1) - 2
      obtain ⟨hN, hM⟩ : 2 ^ (k + 1) - 1 = n + 1 ∧ 2 ^ (k + 2) - 1 = 2 * n + 3 :=
        folded_sizes k
      obtain ⟨R, hR⟩ := Dv_parity (2 * n + 3) (isSign_star n _)
      rw [hN] at hA
      refine ⟨2 * A + 2 * A ^ 2 - R, ?_⟩
      rw [hM]
      have : f (2 * n + 3) = (1 + 2 * A) ^ 2 - 2 * R := by
        rw [← hA, ← Dv_star, hR]; ring
      rw [this]
      ring
end Corless
