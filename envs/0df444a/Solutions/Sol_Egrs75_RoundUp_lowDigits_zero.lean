-- Prove2me | solution 1 for Egrs75.RoundUp.lowDigits_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T17:26:49.892127+00:00
-- url     : https://prove2.me/submissions/59ea532d-1801-478a-a7ae-161687ddbddf

module
public import Definitions.Def_LeanPool_Egrs75_Defs
public import Mathlib.Algebra.Order.SuccPred
public import Mathlib.Data.Finset.Attr
public import Definitions.Def_LeanPool_Egrs75_RoundUp

set_option autoImplicit true
@[expose] public section
public section
open Egrs75 Egrs75.RoundUp
open Nat
open Egrs75
variable (p : ℕ)
namespace Egrs75.RoundUp
theorem _root_.solution (p : ℕ) : LowDigits p 0 := by
  unfold LowDigits
  simp_all
end Egrs75.RoundUp
