-- Prove2me | solution 1 for GJKKL.History.expect_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T13:01:38.459657+00:00
-- url     : https://prove2.me/submissions/fbad009e-f85b-4ce2-961e-113adcc9f433

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
theorem _root_.solution {T : ℕ} {f : List α → ℝ} (hf : ∀ h, h.length = T → 0 ≤ f h) :
    0 ≤ expect κ T f :=
  sum_nonneg fun h hh => mul_nonneg (weight_nonneg κ h) (hf h (mem_hist.mp hh))
end GJKKL.History
