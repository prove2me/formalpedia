-- Prove2me | solution 1 for FD1D.FiniteKernel.iterate_dirac
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T09:42:43.094844+00:00
-- url     : https://prove2.me/submissions/47dadc5c-8756-475e-8222-8458687f4308

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
    (n : ℕ) (x y : α) :
    (K.iterate n (FiniteLaw.dirac x)).mass y = K.pow n x y := by
  rw [mass_iterate]
  simp [FiniteLaw.mass_dirac]
end FD1D.FiniteKernel
