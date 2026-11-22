-- Prove2me | solution 1 for GJKKL.History.expect_const_mul
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T12:48:45.572057+00:00
-- url     : https://prove2.me/submissions/09b54ec4-8bbe-45b4-b637-44c10acff72a

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
theorem _root_.solution (T : ℕ) (c : ℝ) (f : List α → ℝ) :
    expect κ T (fun h => c * f h) = c * expect κ T f := by
  unfold expect
  rw [mul_sum]
  exact sum_congr rfl fun h _ => by ring
end GJKKL.History
