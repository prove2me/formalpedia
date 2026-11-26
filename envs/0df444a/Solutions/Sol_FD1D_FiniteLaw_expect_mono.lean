-- Prove2me | solution 1 for FD1D.FiniteLaw.expect_mono
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T09:32:31.281942+00:00
-- url     : https://prove2.me/submissions/1b811111-b617-4514-a0a7-614df34e8566

import Mathlib
import Definitions.Def_FD1D_Basic

set_option autoImplicit true
open FD1D
noncomputable section
open FD1D.FiniteLaw
variable {α β : Type*} [Fintype α] [Fintype β]
namespace FD1D.FiniteLaw
theorem _root_.solution (μ : FiniteLaw α) {f g : α → ℝ}
    (hfg : ∀ x, f x ≤ g x) : μ.expect f ≤ μ.expect g := by
  apply Finset.sum_le_sum
  intro x _
  exact mul_le_mul_of_nonneg_left (hfg x) (μ.mass_nonneg x)
end FD1D.FiniteLaw
