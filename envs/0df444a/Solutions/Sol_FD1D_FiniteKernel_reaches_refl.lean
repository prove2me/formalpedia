-- Prove2me | solution 1 for FD1D.FiniteKernel.reaches_refl
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T09:43:42.232918+00:00
-- url     : https://prove2.me/submissions/bcbe438a-ad73-48db-97da-c2aa08def2c3

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
theorem _root_.solution [DecidableEq α] (K : FiniteKernel α) (x : α) :
    K.Reaches x x := by
  exact ⟨0, by simp [pow_zero]⟩
end FD1D.FiniteKernel
