-- Prove2me | solution 1 for GJKKL.History.prob_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T13:03:09.515794+00:00
-- url     : https://prove2.me/submissions/b54b5ffc-aed0-41f1-9714-bc1d4b7a9f4c

module
public import Mathlib
public import Definitions.Def_GJKKL_History_Basic
public import Theorems.Thm_GJKKL_History_expect_nonneg

set_option autoImplicit true
@[expose] public section
public section
open GJKKL GJKKL.History
open Finset
variable {α : Type*} [Fintype α] [DecidableEq α]
variable (κ : Kernel α)
namespace GJKKL.History
theorem _root_.solution (T : ℕ) (P : List α → Prop) : 0 ≤ prob κ T P := by
  classical
  unfold prob
  exact expect_nonneg κ fun h _ => by split_ifs <;> norm_num
end GJKKL.History
