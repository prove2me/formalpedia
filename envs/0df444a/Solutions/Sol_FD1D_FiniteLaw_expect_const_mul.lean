-- Prove2me | solution 1 for FD1D.FiniteLaw.expect_const_mul
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T09:45:05.791655+00:00
-- url     : https://prove2.me/submissions/9708603b-e88e-47d9-8022-bb15adaf35e7

import Definitions.Def_FD1D_Markov
import Definitions.Def_FD1D_Expectations

set_option autoImplicit true
open FD1D
noncomputable section
open scoped BigOperators
open FD1D.FiniteLaw
variable {α : Type*} [Fintype α]
namespace FD1D.FiniteLaw
theorem _root_.solution (μ : FiniteLaw α) (c : ℝ) (f : α → ℝ) :
    μ.expect (fun x => c * f x) = c * μ.expect f := by
  rw [expect, expect, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro x _
  ring
end FD1D.FiniteLaw
