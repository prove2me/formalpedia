-- Prove2me | solution 1 for FD1D.FiniteLaw.expect_eq_zero_of_oddSymmetry
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T10:30:38.203806+00:00
-- url     : https://prove2.me/submissions/f9706fed-d3e4-4f02-8f6d-c06cc36c7475

import Definitions.Def_FD1D_Basic
import Definitions.Def_FD1D_Transport
import Theorems.Thm_FD1D_FiniteLaw_expect_comp_equiv
import Theorems.Thm_FD1D_FiniteLaw_expect_const
attribute [local simp] FD1D.FiniteLaw.expect_const



set_option autoImplicit true
open FD1D
noncomputable section
open scoped BigOperators ENNReal NNReal Topology
open Set MeasureTheory intervalIntegral
open FD1D.FiniteLaw
variable {Ω : Type*} [Fintype Ω]
namespace FD1D.FiniteLaw
theorem _root_.solution (μ : FiniteLaw Ω) (f : Ω → ℝ)
    (hodd : OddSymmetry μ f) :
    μ.expect f = 0 := by
  rcases hodd with ⟨e, he, hflip⟩
  have hneg : μ.expect f = -μ.expect f := by
    calc
      μ.expect f = μ.expect (fun ω => f (e ω)) :=
        (expect_comp_equiv μ e he f).symm
      _ = -μ.expect f := by
        simp_rw [hflip]
        simp [expect]
  linarith
end FD1D.FiniteLaw
