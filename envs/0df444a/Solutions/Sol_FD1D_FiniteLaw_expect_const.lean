-- Prove2me | solution 1 for FD1D.FiniteLaw.expect_const
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T09:32:20.727848+00:00
-- url     : https://prove2.me/submissions/df7f97b0-08ad-4c49-b2b2-6f34a7011a79

import Mathlib
import Definitions.Def_FD1D_Basic

set_option autoImplicit true
open FD1D
noncomputable section
open FD1D.FiniteLaw
variable {α β : Type*} [Fintype α] [Fintype β]
namespace FD1D.FiniteLaw
theorem _root_.solution (μ : FiniteLaw α) (c : ℝ) :
    μ.expect (fun _ => c) = c := by
  simp [expect, ← Finset.sum_mul, μ.sum_mass]
end FD1D.FiniteLaw
