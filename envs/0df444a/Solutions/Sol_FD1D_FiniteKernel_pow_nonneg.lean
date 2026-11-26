-- Prove2me | solution 1 for FD1D.FiniteKernel.pow_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T09:39:39.181667+00:00
-- url     : https://prove2.me/submissions/d0ea883f-1b11-4e46-84d6-35888f88d562

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
theorem _root_.solution [DecidableEq α] (K : FiniteKernel α) (n : ℕ) (x y : α) :
    0 ≤ K.pow n x y := by
  have hpow : K.matrix ^ n ∈ Matrix.rowStochastic ℝ α :=
    (Matrix.rowStochastic ℝ α).pow_mem K.matrix_rowStochastic n
  exact Matrix.nonneg_of_mem_rowStochastic
    hpow
end FD1D.FiniteKernel
