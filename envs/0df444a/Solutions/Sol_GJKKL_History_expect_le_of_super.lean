-- Prove2me | solution 1 for GJKKL.History.expect_le_of_super
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T13:03:55.338016+00:00
-- url     : https://prove2.me/submissions/89171ea0-6b76-4c31-af99-54df632c4a74

module
public import Mathlib
public import Definitions.Def_GJKKL_History_Basic
public import Theorems.Thm_GJKKL_History_weight_nil
public import Theorems.Thm_GJKKL_History_weight_cons
public import Theorems.Thm_GJKKL_History_expect_zero
public import Theorems.Thm_GJKKL_History_expect_succ
public import Theorems.Thm_GJKKL_History_expect_mono
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
theorem _root_.solution (Z : List α → ℝ) (T : ℕ)
    (hsuper : ∀ h : List α, h.length < T → ∑ a, κ.K h a * Z (a :: h) ≤ Z h) :
    expect κ T Z ≤ Z [] := by
  induction T with
  | zero => simp
  | succ T ih =>
    rw [expect_succ]
    exact (expect_mono κ fun h hh => hsuper h (by omega)).trans
      (ih fun h hh => hsuper h (by omega))
end GJKKL.History
