-- Prove2me | solution 1 for FD1D.FiniteLaw.expect_sub
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T09:41:25.795084+00:00
-- url     : https://prove2.me/submissions/3e3d61ba-ccc7-4ae8-aac4-f4bd9844a6a9

import Definitions.Def_FD1D_Markov
import Definitions.Def_FD1D_Expectations
import Theorems.Thm_FD1D_DeletionRule_kernel_apply
import Theorems.Thm_FD1D_FiniteLaw_expect_const
attribute [local simp] FD1D.DeletionRule.kernel_apply
attribute [local simp] FD1D.FiniteLaw.expect_const



set_option autoImplicit true
open FD1D
noncomputable section
open scoped BigOperators
open FD1D.FiniteLaw
variable {α : Type*} [Fintype α]
namespace FD1D.FiniteLaw
theorem _root_.solution (μ : FiniteLaw α) (f g : α → ℝ) :
    μ.expect (fun x => f x - g x) = μ.expect f - μ.expect g := by
  simp [expect, mul_sub, Finset.sum_sub_distrib]
end FD1D.FiniteLaw
