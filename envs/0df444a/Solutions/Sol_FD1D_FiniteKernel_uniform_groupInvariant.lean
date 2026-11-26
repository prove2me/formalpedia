-- Prove2me | solution 1 for FD1D.FiniteKernel.uniform_groupInvariant
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T09:39:41.042523+00:00
-- url     : https://prove2.me/submissions/c4a9f7b1-8f19-4c8b-9475-c9ea265b3e46

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
theorem _root_.solution [Nonempty α]
    {G : Type*} [Group G] (ρ : G →* Equiv.Perm α) :
    GroupInvariant ρ (FiniteLaw.uniform : FiniteLaw α) := by
  intro g x
  rfl
end FD1D.FiniteKernel
