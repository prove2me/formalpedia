-- Prove2me | solution 1 for FD1D.FiniteKernel.sum_pow
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T09:42:34.729947+00:00
-- url     : https://prove2.me/submissions/907d9a3b-1e8a-407b-9b8d-9e6345a353a2

import Definitions.Def_FD1D_Basic
import Definitions.Def_FD1D_Markov
import Theorems.Thm_FD1D_FiniteKernel_matrix_rowStochastic

set_option autoImplicit true
open FD1D
noncomputable section
open scoped BigOperators Topology
open Filter Matrix
open FD1D.FiniteKernel
variable {α β : Type*} [Fintype α] [Fintype β]
namespace FD1D.FiniteKernel
theorem _root_.solution [DecidableEq α] (K : FiniteKernel α) (n : ℕ) (x : α) :
    ∑ y, K.pow n x y = 1 := by
  have hpow : K.matrix ^ n ∈ Matrix.rowStochastic ℝ α :=
    (Matrix.rowStochastic ℝ α).pow_mem K.matrix_rowStochastic n
  exact Matrix.sum_row_of_mem_rowStochastic hpow x
end FD1D.FiniteKernel
