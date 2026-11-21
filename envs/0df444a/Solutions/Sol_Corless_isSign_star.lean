-- Prove2me | solution 1 for Corless.isSign_star
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-20T22:40:47.00904+00:00
-- url     : https://prove2.me/submissions/1633770c-09f9-4d48-afe1-44d2de3947bf

module
public import Mathlib.Algebra.CharP.Lemmas
public import Mathlib.Algebra.CharP.Reduced
public import Mathlib.Algebra.Field.ZMod
public import Mathlib.Algebra.Polynomial.Eval.Coeff
public import Mathlib.Tactic.LinearCombination
public import Definitions.Def_LeanPool_CorlessNilpotent_Path
public import Definitions.Def_LeanPool_CorlessNilpotent_Parity
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
theorem _root_.solution (n m : ℕ) : IsSign (star n) m := fun i _ => by
  by_cases h : i = n + 1 <;> simp [star, h]
end Corless
