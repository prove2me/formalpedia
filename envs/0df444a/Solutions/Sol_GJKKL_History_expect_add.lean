-- Prove2me | solution 1 for GJKKL.History.expect_add
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T12:48:41.856456+00:00
-- url     : https://prove2.me/submissions/9ad28642-87ce-4730-81be-acb7df6d2c4a

module
public import Mathlib
public import Definitions.Def_GJKKL_History_Basic

set_option autoImplicit true
@[expose] public section
public section
open GJKKL GJKKL.History
open Finset
variable {α : Type*} [Fintype α] [DecidableEq α]
variable (κ : Kernel α)
namespace GJKKL.History
theorem _root_.solution (T : ℕ) (f g : List α → ℝ) :
    expect κ T (fun h => f h + g h) = expect κ T f + expect κ T g := by
  unfold expect
  rw [← sum_add_distrib]
  exact sum_congr rfl fun h _ => by ring
end GJKKL.History
