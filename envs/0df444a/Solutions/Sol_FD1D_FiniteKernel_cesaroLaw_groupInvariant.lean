-- Prove2me | solution 1 for FD1D.FiniteKernel.cesaroLaw_groupInvariant
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T09:42:36.460965+00:00
-- url     : https://prove2.me/submissions/84a7a9f4-bdf5-40e1-9552-19188065cb22

import Definitions.Def_FD1D_Basic
import Definitions.Def_FD1D_Markov
import Theorems.Thm_FD1D_FiniteKernel_iterate_groupInvariant
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
theorem _root_.solution [DecidableEq α]
    {G : Type*} [Group G] (ρ : G →* Equiv.Perm α)
    {K : FiniteKernel α} {μ : FiniteLaw α}
    (hK : GroupEquivariant ρ K) (hμ : GroupInvariant ρ μ) (n : ℕ) :
    GroupInvariant ρ (K.cesaroLaw μ n) := by
  intro g x
  simp only [cesaroLaw, cesaroVec, Pi.smul_apply, smul_eq_mul,
    Finset.sum_apply]
  apply congrArg (fun z : ℝ => ((↑(n + 1))⁻¹ : ℝ) * z)
  apply Finset.sum_congr rfl
  intro k _
  rw [K.orbit_eq_iterate μ, K.orbit_eq_iterate μ]
  exact iterate_groupInvariant ρ hK hμ k g x
end FD1D.FiniteKernel
