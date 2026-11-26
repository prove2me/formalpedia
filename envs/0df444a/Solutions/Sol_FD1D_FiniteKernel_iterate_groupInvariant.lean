-- Prove2me | solution 1 for FD1D.FiniteKernel.iterate_groupInvariant
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T09:41:25.11783+00:00
-- url     : https://prove2.me/submissions/e504e134-02b2-4933-880c-e085655c90fd

import Definitions.Def_FD1D_Basic
import Definitions.Def_FD1D_Markov
import Theorems.Thm_FD1D_FiniteKernel_iterate_lawInvariant

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
    (hK : GroupEquivariant ρ K) (hμ : GroupInvariant ρ μ) (n : ℕ) :
    GroupInvariant ρ (K.iterate n μ) :=
  fun g => iterate_lawInvariant (hK g) (hμ g) n
end FD1D.FiniteKernel
