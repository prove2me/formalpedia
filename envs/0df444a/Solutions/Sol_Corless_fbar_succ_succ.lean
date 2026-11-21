-- Prove2me | solution 1 for Corless.fbar_succ_succ
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-20T22:42:22.546404+00:00
-- url     : https://prove2.me/submissions/801f9983-b397-4a1a-8cfd-1a45c9c968a5

module
public import Mathlib.Algebra.CharP.Lemmas
public import Mathlib.Algebra.CharP.Reduced
public import Mathlib.Algebra.Field.ZMod
public import Mathlib.Algebra.Polynomial.Eval.Coeff
public import Mathlib.Tactic.LinearCombination
public import Definitions.Def_LeanPool_CorlessNilpotent_Path
public import Definitions.Def_LeanPool_CorlessNilpotent_Parity
public import Theorems.Thm_Corless_f_succ_succ
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
theorem _root_.solution (j : ℕ) : fbar (j + 2) = fbar (j + 1) + X * fbar j := by
  simp [fbar, f_succ_succ, Polynomial.map_add, Polynomial.map_mul]
end Corless
