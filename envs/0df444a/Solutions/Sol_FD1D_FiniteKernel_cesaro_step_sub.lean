-- Prove2me | solution 1 for FD1D.FiniteKernel.cesaro_step_sub
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T09:40:14.689921+00:00
-- url     : https://prove2.me/submissions/6ca66a8d-83d4-4bd3-95de-0117789c8f78

import Definitions.Def_FD1D_Basic
import Definitions.Def_FD1D_Markov
import Theorems.Thm_FD1D_FiniteKernel_orbit_succ
import Theorems.Thm_FD1D_FiniteLaw_expect_const
attribute [local simp] FD1D.FiniteLaw.expect_const



set_option autoImplicit true
open FD1D
noncomputable section
open scoped BigOperators Topology
open Filter Matrix
open FD1D.FiniteKernel
variable {α β : Type*} [Fintype α] [Fintype β]
namespace FD1D.FiniteKernel
theorem _root_.solution [DecidableEq α] (K : FiniteKernel α)
    (μ : FiniteLaw α) (n : ℕ) :
    K.cesaroVec μ n ᵥ* K.matrix - K.cesaroVec μ n =
      ((n + 1 : ℕ) : ℝ)⁻¹ •
        (K.orbit μ (n + 1) - K.orbit μ 0) := by
  simp only [cesaroVec, Matrix.smul_vecMul, Matrix.sum_vecMul]
  rw [← smul_sub, ← Finset.sum_sub_distrib]
  simp_rw [← K.orbit_succ μ]
  rw [Finset.sum_range_sub]
end FD1D.FiniteKernel
