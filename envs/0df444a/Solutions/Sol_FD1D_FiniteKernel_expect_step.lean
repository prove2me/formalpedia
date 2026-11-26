-- Prove2me | solution 1 for FD1D.FiniteKernel.expect_step
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T09:41:35.333012+00:00
-- url     : https://prove2.me/submissions/1d2bdbc9-4211-4be8-aa15-39717eea0c5b

import Definitions.Def_FD1D_Markov
import Definitions.Def_FD1D_Expectations

set_option autoImplicit true
open FD1D
noncomputable section
open scoped BigOperators
open FD1D.FiniteKernel
variable {α : Type*} [Fintype α]
namespace FD1D.FiniteKernel
theorem _root_.solution (K : FiniteKernel α) (μ : FiniteLaw α) (f : α → ℝ) :
    (K.step μ).expect f =
      μ.expect (fun x => ∑ y, K x y * f y) := by
  rw [FiniteLaw.expect, FiniteLaw.expect]
  simp_rw [mass_step, Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro x _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro y _
  ring
end FD1D.FiniteKernel
