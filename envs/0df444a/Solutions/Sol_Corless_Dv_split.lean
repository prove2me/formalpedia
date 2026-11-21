-- Prove2me | solution 1 for Corless.Dv_split
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-20T22:41:34.073426+00:00
-- url     : https://prove2.me/submissions/f667b0c7-dc9a-45c4-aba9-425d5ea1eba3

module
public import Mathlib.Algebra.Polynomial.Basic
public import Mathlib.Tactic.Ring
public import Definitions.Def_LeanPool_CorlessNilpotent_Path
public import Theorems.Thm_Corless_Dv_zero
public import Theorems.Thm_Corless_Dv_one
public import Theorems.Thm_Corless_Dv_succ_succ
attribute [local simp] Corless.Dv_zero
attribute [local simp] Corless.Dv_one

set_option autoImplicit true
@[expose] public section
public section
open Polynomial Finset
open Corless
namespace Corless
theorem _root_.solution (s : ℕ → ℤ) (k : ℕ) : ∀ m : ℕ,
    Dv s (k + m + 2) = Dv s (k + 1) * Dv (fun i => s (i + k + 1)) (m + 1)
      + C (s k) * X * Dv s k * Dv (fun i => s (i + k + 2)) m
  | 0 => by simp [Dv_succ_succ]
  | 1 => by
      have e : s (0 + k + 1) = s (k + 1) := by congr 1; omega
      rw [Dv_succ_succ, Dv_succ_succ s k,
        show (1 : ℕ) + 1 = 0 + 2 by rfl, Dv_succ_succ (fun i => s (i + k + 1)) 0, e]
      simp only [Dv_zero, zero_add, Dv_one]
      ring
  | m + 2 => by
      have h1 := solution s k (m + 1)
      have h0 := solution s k m
      have e1 : s (m + 1 + k + 1) = s (k + m + 2) := by congr 1; omega
      have e2 : s (m + k + 2) = s (k + m + 2) := by congr 1; omega
      rw [show k + (m + 2) + 2 = (k + m + 2) + 2 by omega, Dv_succ_succ,
        show (k + m + 2) + 1 = k + (m + 1) + 2 by omega,
        show m + 2 + 1 = (m + 1) + 2 by omega, Dv_succ_succ (fun i => s (i + k + 1)) (m + 1),
        Dv_succ_succ (fun i => s (i + k + 2)) m, e1, e2, h1, h0]
      ring
end Corless
