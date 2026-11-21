-- Prove2me | solution 1 for Corless.Dv_star
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-20T22:43:54.546337+00:00
-- url     : https://prove2.me/submissions/5b94d539-d111-4317-9204-fd7118023101

module
public import Mathlib.Algebra.CharP.Lemmas
public import Mathlib.Algebra.CharP.Reduced
public import Mathlib.Algebra.Field.ZMod
public import Mathlib.Algebra.Polynomial.Eval.Coeff
public import Mathlib.Tactic.LinearCombination
public import Definitions.Def_LeanPool_CorlessNilpotent_Path
public import Definitions.Def_LeanPool_CorlessNilpotent_Parity
public import Theorems.Thm_Corless_Dv_fold
public import Theorems.Thm_Corless_Dv_congr
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
theorem _root_.solution (n : ℕ) : Dv (star n) (2 * n + 3) = f (n + 1) ^ 2 := by
  rw [Dv_fold]
  · congr 1
    apply Dv_congr
    intro i hi
    have : i ≠ n + 1 := by omega
    simp [star, this]
  · constructor
    · simp [star]
    · intro i hi
      have h1 : 2 * n + 1 - i ≠ n + 1 := by omega
      have h2 : i ≠ n + 1 := by omega
      simp [star, h1, h2]
end Corless
