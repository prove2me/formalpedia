-- Prove2me | solution 1 for FD1D.FiniteKernel.reaches_of_pos
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T09:43:44.365953+00:00
-- url     : https://prove2.me/submissions/86b53630-391a-4b30-a572-416a031802f2

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
    {x y : α} (h : 0 < K x y) : K.Reaches x y := by
  exact ⟨1, by simpa using h⟩
end FD1D.FiniteKernel
