-- Prove2me | solution 1 for GJKKL.History.sum_hist_succ
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T13:01:18.155821+00:00
-- url     : https://prove2.me/submissions/6a3e94d1-9622-4483-a4dc-ce6318fa80f1

module
public import Mathlib
public import Definitions.Def_GJKKL_History_Basic

set_option autoImplicit true
@[expose] public section
public section
open GJKKL GJKKL.History
open Finset
variable {α : Type*} [Fintype α] [DecidableEq α]
namespace GJKKL.History
theorem _root_.solution (T : ℕ) (F : List α → ℝ) :
    ∑ h ∈ hist α (T + 1), F h = ∑ h ∈ hist α T, ∑ a, F (a :: h) := by
  rw [hist, sum_image (fun p _ q _ hpq => by
    simp only [List.cons.injEq] at hpq
    exact Prod.ext hpq.1 hpq.2)]
  rw [sum_product, sum_comm]
end GJKKL.History
