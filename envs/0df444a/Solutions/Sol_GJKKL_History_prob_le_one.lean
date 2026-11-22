-- Prove2me | solution 1 for GJKKL.History.prob_le_one
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T13:26:35.818616+00:00
-- url     : https://prove2.me/submissions/fbcf753b-9e76-4ccd-af3b-0f4dab081eb6

module
public import Mathlib
public import Definitions.Def_GJKKL_History_Basic
public import Theorems.Thm_GJKKL_History_expect_mono
public import Theorems.Thm_GJKKL_History_expect_one_le

set_option autoImplicit true
@[expose] public section
public section
open GJKKL GJKKL.History
open Finset
variable {α : Type*} [Fintype α] [DecidableEq α]
variable (κ : Kernel α)
namespace GJKKL.History
theorem _root_.solution (T : ℕ) (P : List α → Prop) : prob κ T P ≤ 1 := by
  classical
  unfold prob
  refine (expect_mono κ fun h _ => ?_).trans (expect_one_le κ T)
  split_ifs <;> norm_num
end GJKKL.History
