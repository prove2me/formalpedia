-- Prove2me | solution 1 for Corless.eq_one_of_sq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-20T22:42:33.685213+00:00
-- url     : https://prove2.me/submissions/45dae3b7-e11a-42df-9930-e21227abbf37

module
public import Mathlib.Algebra.BigOperators.Intervals
public import Definitions.Def_LeanPool_CorlessNilpotent_Parity
public import Definitions.Def_LeanPool_CorlessNilpotent_Main
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
theorem _root_.solution {p : ℤ[X]} (h : p ^ 2 = 1) (h0 : p.coeff 0 = 1) : p = 1 := by
  have : (p - 1) * (p + 1) = 0 := by linear_combination h
  rcases mul_eq_zero.mp this with h1 | h1
  · exact sub_eq_zero.mp h1
  · have := congrArg (fun q => q.coeff 0) h1
    simp [h0] at this
end Corless
