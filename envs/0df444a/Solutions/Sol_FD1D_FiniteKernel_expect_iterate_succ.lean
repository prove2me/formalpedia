-- Prove2me | solution 1 for FD1D.FiniteKernel.expect_iterate_succ
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T09:45:17.314242+00:00
-- url     : https://prove2.me/submissions/6d49acea-c647-4174-bea1-9828f57af230

import Definitions.Def_FD1D_Markov
import Definitions.Def_FD1D_Expectations
import Theorems.Thm_FD1D_FiniteKernel_expect_step_sub

set_option autoImplicit true
open FD1D
noncomputable section
open scoped BigOperators
open FD1D.FiniteKernel
variable {α : Type*} [Fintype α]
namespace FD1D.FiniteKernel
theorem _root_.solution (K : FiniteKernel α) (μ : FiniteLaw α)
    (n : ℕ) (f : α → ℝ) :
    (K.iterate (n + 1) μ).expect f - (K.iterate n μ).expect f =
      (K.iterate n μ).expect
        (fun x => ∑ y, K x y * (f y - f x)) := by
  rw [iterate_succ]
  exact K.expect_step_sub (K.iterate n μ) f
end FD1D.FiniteKernel
