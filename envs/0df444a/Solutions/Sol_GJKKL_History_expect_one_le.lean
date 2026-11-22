-- Prove2me | solution 1 for GJKKL.History.expect_one_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T13:05:24.263959+00:00
-- url     : https://prove2.me/submissions/7bc46085-4113-4972-abbe-2b9e0af816b2

module
public import Mathlib
public import Definitions.Def_GJKKL_History_Basic
public import Theorems.Thm_GJKKL_History_weight_nil
public import Theorems.Thm_GJKKL_History_weight_cons
public import Theorems.Thm_GJKKL_History_expect_zero
public import Theorems.Thm_GJKKL_History_expect_le_of_super
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
theorem _root_.solution (T : ℕ) : expect κ T (fun _ => 1) ≤ 1 := by
  have := expect_le_of_super κ (fun _ => (1 : ℝ)) T fun h _ => by
    simpa using κ.mass_le h
  simpa using this
end GJKKL.History
