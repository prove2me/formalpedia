-- Prove2me | solution 1 for GJKKL.History.sum_K_mul_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T12:50:39.054674+00:00
-- url     : https://prove2.me/submissions/58c89b25-8d8c-4886-8af9-fae082b2ee36

module
public import Definitions.Def_GJKKL_History_Freedman
public import Definitions.Def_GJKKL_History_FirstFailure

set_option autoImplicit true
@[expose] public section
public section
open GJKKL GJKKL.History
open Finset
variable {α : Type*} [Fintype α] [DecidableEq α] (κ : Kernel α) (G : List α → Prop)
namespace GJKKL.History
theorem _root_.solution (h : List α) {f : α → ℝ} {c : ℝ} (hf : ∀ a, f a ≤ c) (hc : 0 ≤ c) :
    ∑ a, κ.K h a * f a ≤ c := by
  calc ∑ a, κ.K h a * f a ≤ ∑ a, κ.K h a * c :=
        sum_le_sum fun a _ => mul_le_mul_of_nonneg_left (hf a) (κ.nonneg h a)
    _ = (∑ a, κ.K h a) * c := by rw [sum_mul]
    _ ≤ c := mul_le_of_le_one_left hc (κ.mass_le h)
end GJKKL.History
