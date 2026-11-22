-- Prove2me | solution 1 for GJKKL.History.expect_succ
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T13:02:37.215588+00:00
-- url     : https://prove2.me/submissions/795a7c36-6921-453d-8708-23c30b7f3041

module
public import Mathlib
public import Definitions.Def_GJKKL_History_Basic
public import Theorems.Thm_GJKKL_History_sum_hist_succ
public import Theorems.Thm_GJKKL_History_weight_nil
public import Theorems.Thm_GJKKL_History_weight_cons
public import Theorems.Thm_GJKKL_History_expect_zero
attribute [local simp] GJKKL.History.weight_nil
attribute [local simp] GJKKL.History.weight_cons
attribute [local simp] GJKKL.History.expect_zero

set_option autoImplicit true
@[expose] public section
public section
open GJKKL GJKKL.History
open Finset
variable {α : Type*} [Fintype α] [DecidableEq α]
variable (κ : Kernel α)
namespace GJKKL.History
theorem _root_.solution (T : ℕ) (f : List α → ℝ) :
    expect κ (T + 1) f = expect κ T (fun h => ∑ a, κ.K h a * f (a :: h)) := by
  unfold expect
  rw [sum_hist_succ]
  refine sum_congr rfl fun h _ => ?_
  rw [mul_sum]
  refine sum_congr rfl fun a _ => ?_
  simp only [weight_cons]
  ring
end GJKKL.History
