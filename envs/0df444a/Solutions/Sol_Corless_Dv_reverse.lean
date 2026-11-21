-- Prove2me | solution 1 for Corless.Dv_reverse
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-20T22:42:44.593178+00:00
-- url     : https://prove2.me/submissions/3be59ab6-23e3-4111-b634-2d259e4ca027

module
public import Mathlib.Algebra.Polynomial.Basic
public import Mathlib.Tactic.Ring
public import Definitions.Def_LeanPool_CorlessNilpotent_Path
public import Theorems.Thm_Corless_Dv_zero
public import Theorems.Thm_Corless_Dv_one
public import Theorems.Thm_Corless_Dv_succ_succ
public import Theorems.Thm_Corless_Dv_congr
public import Theorems.Thm_Corless_Dv_succ_succ_left
attribute [local simp] Corless.Dv_zero
attribute [local simp] Corless.Dv_one

set_option autoImplicit true
@[expose] public section
public section
open Polynomial Finset
open Corless
namespace Corless
theorem _root_.solution (s : ℕ → ℤ) : ∀ j : ℕ, Dv (fun i => s (j - 2 - i)) j = Dv s j
  | 0 => by simp
  | 1 => by simp
  | j + 2 => by
      rw [Dv_succ_succ, Dv_succ_succ_left s j]
      have h1 : Dv (fun i => s (j + 2 - 2 - i)) (j + 1) = Dv (fun i => s (i + 1)) (j + 1) := by
        rw [← solution (fun i => s (i + 1)) (j + 1)]
        apply Dv_congr
        intro i hi
        congr 1
        omega
      have h0 : Dv (fun i => s (j + 2 - 2 - i)) j = Dv (fun i => s (i + 2)) j := by
        rw [← solution (fun i => s (i + 2)) j]
        apply Dv_congr
        intro i hi
        congr 1
        omega
      have e : s (j + 2 - 2 - j) = s 0 := by congr 1; omega
      rw [h1, h0, e]
end Corless
