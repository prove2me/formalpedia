-- Prove2me | solution 1 for GJKKL.History.expect_congr
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T13:01:28.355086+00:00
-- url     : https://prove2.me/submissions/5fc629a3-92ad-44d7-a452-84aa15d7f689

module
public import Mathlib
public import Definitions.Def_GJKKL_History_Basic
public import Theorems.Thm_GJKKL_History_mem_hist

set_option autoImplicit true
@[expose] public section
public section
open GJKKL GJKKL.History
open Finset
variable {α : Type*} [Fintype α] [DecidableEq α]
variable (κ : Kernel α)
namespace GJKKL.History
theorem _root_.solution {T : ℕ} {f g : List α → ℝ} (hfg : ∀ h, h.length = T → f h = g h) :
    expect κ T f = expect κ T g :=
  sum_congr rfl fun h hh => by rw [hfg h (mem_hist.mp hh)]
end GJKKL.History
