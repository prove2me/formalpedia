-- Prove2me | solution 1 for GJKKL.History.expect_mono
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T12:33:51.162679+00:00
-- url     : https://prove2.me/submissions/9919161b-323e-4f63-a1b4-5ef30bb82b83

module
public import Mathlib
public import Definitions.Def_GJKKL_History_Basic
public import Theorems.Thm_GJKKL_History_mem_hist
public import Theorems.Thm_GJKKL_History_weight_nonneg

set_option autoImplicit true
@[expose] public section
public section
open GJKKL GJKKL.History
open Finset
variable {α : Type*} [Fintype α] [DecidableEq α]
variable (κ : Kernel α)
namespace GJKKL.History
theorem _root_.solution {T : ℕ} {f g : List α → ℝ} (hfg : ∀ h, h.length = T → f h ≤ g h) :
    expect κ T f ≤ expect κ T g :=
  sum_le_sum fun h hh => mul_le_mul_of_nonneg_left (hfg h (mem_hist.mp hh)) (weight_nonneg κ h)
end GJKKL.History
