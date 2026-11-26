-- Prove2me | solution 1 for FD1D.FiniteKernel.orbit_succ
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T09:38:54.500676+00:00
-- url     : https://prove2.me/submissions/8986cce8-e309-42c6-8eed-f869c2269f01

import Definitions.Def_FD1D_Basic
import Definitions.Def_FD1D_Markov
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
    K.orbit μ (n + 1) = K.orbit μ n ᵥ* K.matrix := by
  simp only [orbit, _root_.pow_succ, Matrix.vecMul_vecMul]
end FD1D.FiniteKernel
