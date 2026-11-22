-- Prove2me | solution 1 for Egrs75.RoundUp.lowDigits_one
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T17:30:24.185894+00:00
-- url     : https://prove2.me/submissions/ffe2daa9-ff4d-4dd5-9e94-8f81285f134b

module
public import Definitions.Def_LeanPool_Egrs75_Defs
public import Mathlib.Algebra.Order.SuccPred
public import Mathlib.Data.Finset.Attr
public import Definitions.Def_LeanPool_Egrs75_RoundUp
public import Theorems.Thm_Egrs75_RoundUp_lowDigits_zero
public import Theorems.Thm_Egrs75_RoundUp_lowDigits_cons
public import Theorems.Thm_Egrs75_RoundUp_one_le_half

set_option autoImplicit true
@[expose] public section
public section
open Egrs75 Egrs75.RoundUp
open Nat
open Egrs75
variable (p : ℕ)
namespace Egrs75.RoundUp
theorem _root_.solution {p : ℕ} (hp : 3 ≤ p) : LowDigits p 1 := by
  have h : (1 : ℕ) = p * 0 + 1 := by ring
  rw [h]
  exact lowDigits_cons (by omega) (one_le_half hp) (lowDigits_zero p)
end Egrs75.RoundUp
