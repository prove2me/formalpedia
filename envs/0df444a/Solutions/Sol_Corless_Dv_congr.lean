-- Prove2me | solution 1 for Corless.Dv_congr
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-20T22:41:32.922579+00:00
-- url     : https://prove2.me/submissions/50ae82f1-de9e-4f4d-be93-201aed33812f

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
theorem _root_.solution {s t : ℕ → ℤ} : ∀ {j : ℕ}, (∀ i, i + 1 < j → s i = t i) → Dv s j = Dv t j
  | 0, _ => by simp
  | 1, _ => by simp
  | j + 2, h => by
      rw [Dv_succ_succ, Dv_succ_succ, solution (j := j + 1) (fun i hi => h i (by omega)),
        solution (j := j) (fun i hi => h i (by omega)), h j (by omega)]
end Corless
