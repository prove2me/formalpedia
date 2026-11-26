-- Prove2me | solution 1 for FD1D.FiniteKernel.iterate_add
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T09:42:25.131099+00:00
-- url     : https://prove2.me/submissions/cdfb8e1a-e292-44b4-8de3-641e39a9cc3e

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
theorem _root_.solution (K : FiniteKernel α) (m n : ℕ) (μ : FiniteLaw α) :
    K.iterate (m + n) μ = K.iterate m (K.iterate n μ) := by
  induction m with
  | zero => simp
  | succ m ih =>
      rw [Nat.succ_add, iterate_succ, ih, iterate_succ]
end FD1D.FiniteKernel
