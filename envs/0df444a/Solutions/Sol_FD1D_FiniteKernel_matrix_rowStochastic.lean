-- Prove2me | solution 1 for FD1D.FiniteKernel.matrix_rowStochastic
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T09:38:36.675956+00:00
-- url     : https://prove2.me/submissions/b82a85e6-5259-4688-b0f9-c6ed025c0569

import Definitions.Def_FD1D_Basic
import Definitions.Def_FD1D_Markov

set_option autoImplicit true
open FD1D
noncomputable section
open scoped BigOperators Topology
open Filter Matrix
open FD1D.FiniteKernel
variable {α β : Type*} [Fintype α] [Fintype β]
namespace FD1D.FiniteKernel
theorem _root_.solution [DecidableEq α] (K : FiniteKernel α) :
    K.matrix ∈ Matrix.rowStochastic ℝ α := by
  rw [Matrix.mem_rowStochastic_iff_sum]
  exact ⟨K.trans_nonneg, K.sum_trans⟩
end FD1D.FiniteKernel
