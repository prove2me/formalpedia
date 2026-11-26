-- Prove2me | solution 1 for FD1D.FiniteLaw.expect_mul_const
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T09:45:11.981803+00:00
-- url     : https://prove2.me/submissions/dbb00ac5-2e68-40ae-97be-cbb2bbc154a5

import Definitions.Def_FD1D_Markov
import Definitions.Def_FD1D_Expectations

set_option autoImplicit true
open FD1D
noncomputable section
open scoped BigOperators
open FD1D.FiniteLaw
variable {α : Type*} [Fintype α]
namespace FD1D.FiniteLaw
theorem _root_.solution (μ : FiniteLaw α) (f : α → ℝ) (c : ℝ) :
    μ.expect (fun x => f x * c) = μ.expect f * c := by
  rw [expect, expect, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro x _
  ring
end FD1D.FiniteLaw
