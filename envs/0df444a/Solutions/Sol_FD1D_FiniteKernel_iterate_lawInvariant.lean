-- Prove2me | solution 1 for FD1D.FiniteKernel.iterate_lawInvariant
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T09:39:36.103156+00:00
-- url     : https://prove2.me/submissions/3b04cfd0-e43a-4e62-a869-d00d12bd63d8

import Definitions.Def_FD1D_Basic
import Definitions.Def_FD1D_Markov
import Theorems.Thm_FD1D_FiniteKernel_step_lawInvariant

set_option autoImplicit true
open FD1D
noncomputable section
open scoped BigOperators Topology
open Filter Matrix
open FD1D.FiniteKernel
variable {α β : Type*} [Fintype α] [Fintype β]
namespace FD1D.FiniteKernel
theorem _root_.solution [DecidableEq α] {K : FiniteKernel α}
    {μ : FiniteLaw α} {e : Equiv.Perm α}
    (hK : K.Equivariant e) (hμ : LawInvariant μ e) (n : ℕ) :
    LawInvariant (K.iterate n μ) e := by
  induction n with
  | zero => exact hμ
  | succ n ih =>
      rw [iterate_succ]
      exact step_lawInvariant hK ih
end FD1D.FiniteKernel
