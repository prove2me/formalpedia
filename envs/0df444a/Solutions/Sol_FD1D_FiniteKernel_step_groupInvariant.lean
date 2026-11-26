-- Prove2me | solution 1 for FD1D.FiniteKernel.step_groupInvariant
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T09:44:05.055157+00:00
-- url     : https://prove2.me/submissions/5ed5273d-9026-49b9-9cfd-c962833d4668

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
theorem _root_.solution [DecidableEq α]
    {G : Type*} [Group G] (ρ : G →* Equiv.Perm α)
    {K : FiniteKernel α} {μ : FiniteLaw α}
    (hK : GroupEquivariant ρ K) (hμ : GroupInvariant ρ μ) :
    GroupInvariant ρ (K.step μ) :=
  fun g => step_lawInvariant (hK g) (hμ g)
end FD1D.FiniteKernel
