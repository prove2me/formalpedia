-- Prove2me | solution 1 for FD1D.FiniteLaw.expect_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T09:32:21.306497+00:00
-- url     : https://prove2.me/submissions/606c7eef-6322-4d34-b89a-fa50a75ba444

import Mathlib
import Definitions.Def_FD1D_Basic

set_option autoImplicit true
open FD1D
noncomputable section
open FD1D.FiniteLaw
variable {α β : Type*} [Fintype α] [Fintype β]
namespace FD1D.FiniteLaw
theorem _root_.solution (μ : FiniteLaw α) {f : α → ℝ}
    (hf : ∀ x, 0 ≤ f x) : 0 ≤ μ.expect f := by
  exact Finset.sum_nonneg fun x _ => mul_nonneg (μ.mass_nonneg x) (hf x)
end FD1D.FiniteLaw
