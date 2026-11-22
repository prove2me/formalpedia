-- Prove2me | solution 1 for GJKKL.History.expect_const_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T13:25:29.264961+00:00
-- url     : https://prove2.me/submissions/4192e88e-74ed-47f2-b057-3b2fd7abfa1b

module
public import Mathlib
public import Definitions.Def_GJKKL_History_Basic
public import Theorems.Thm_GJKKL_History_weight_nil
public import Theorems.Thm_GJKKL_History_weight_cons
public import Theorems.Thm_GJKKL_History_expect_zero
public import Theorems.Thm_GJKKL_History_expect_const_mul
public import Theorems.Thm_GJKKL_History_expect_one_le
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
theorem _root_.solution {c : ℝ} (hc : 0 ≤ c) (T : ℕ) : expect κ T (fun _ => c) ≤ c := by
  have := expect_const_mul κ T c (fun _ => 1)
  simp only [mul_one] at this
  rw [this]
  exact mul_le_of_le_one_right hc (expect_one_le κ T)
end GJKKL.History
