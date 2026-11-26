-- Prove2me | solution 1 for FD1D.FiniteKernel.expect_step_sub
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T09:42:47.21701+00:00
-- url     : https://prove2.me/submissions/4d178f61-45f5-457a-8006-14546b4cba22

import Definitions.Def_FD1D_Markov
import Definitions.Def_FD1D_Expectations
import Theorems.Thm_FD1D_FiniteLaw_expect_sub
import Theorems.Thm_FD1D_FiniteKernel_expect_step

set_option autoImplicit true
open FD1D
noncomputable section
open scoped BigOperators
open FD1D.FiniteKernel
variable {α : Type*} [Fintype α]
namespace FD1D.FiniteKernel
theorem _root_.solution (K : FiniteKernel α) (μ : FiniteLaw α)
    (f : α → ℝ) :
    (K.step μ).expect f - μ.expect f =
      μ.expect (fun x => ∑ y, K x y * (f y - f x)) := by
  rw [K.expect_step μ f, ← μ.expect_sub]
  apply congrArg μ.expect
  funext x
  simp_rw [mul_sub]
  rw [Finset.sum_sub_distrib, ← Finset.sum_mul, K.sum_trans, one_mul]
end FD1D.FiniteKernel
