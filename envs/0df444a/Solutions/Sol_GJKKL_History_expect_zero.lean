-- Prove2me | solution 1 for GJKKL.History.expect_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T12:32:25.029628+00:00
-- url     : https://prove2.me/submissions/4814848b-ac4a-4e9b-b166-a4f25f59cea8

module
public import Mathlib
public import Definitions.Def_GJKKL_History_Basic
public import Theorems.Thm_GJKKL_History_weight_nil
public import Theorems.Thm_GJKKL_History_weight_cons
attribute [local simp] GJKKL.History.weight_nil
attribute [local simp] GJKKL.History.weight_cons

set_option autoImplicit true
@[expose] public section
public section
open GJKKL GJKKL.History
open Finset
variable {α : Type*} [Fintype α] [DecidableEq α]
variable (κ : Kernel α)
namespace GJKKL.History
theorem _root_.solution (f : List α → ℝ) : expect κ 0 f = f [] := by
  simp [expect, hist]
end GJKKL.History
