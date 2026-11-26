-- Prove2me | solution 1 for FD1D.FiniteKernel.existsUnique_stationary_and_tendsto
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T11:04:37.066092+00:00
-- url     : https://prove2.me/submissions/da9d8626-22c8-4f13-9eaf-ce55e223daf9

import Definitions.Def_FD1D_Expectations
import Definitions.Def_FD1D_FiniteConvergence
import Theorems.Thm_FD1D_FiniteKernel_tendsto_iterate_mass
import Theorems.Thm_FD1D_FiniteKernel_exists_stationary
import Theorems.Thm_FD1D_FiniteKernel_stationary_unique


set_option autoImplicit true
open FD1D
noncomputable section
open Filter
open scoped BigOperators Topology
open FD1D.FiniteKernel
variable {α : Type*} [Fintype α] [DecidableEq α] [Nonempty α]
namespace FD1D.FiniteKernel
theorem _root_.solution
    (K : FiniteKernel α) (hirr : K.Irreducible)
    (hloop : K.HasPositiveLoops) :
    ∃! π : FiniteLaw α,
      K.IsStationary π ∧
        ∀ μ : FiniteLaw α,
          Tendsto (fun n => (K.iterate n μ).mass) atTop (𝓝 π.mass) := by
  obtain ⟨π, hπ⟩ := K.exists_stationary
  refine ⟨π, ⟨hπ, fun μ => tendsto_iterate_mass K hirr hloop π hπ μ⟩, ?_⟩
  intro ν hν
  exact K.stationary_unique hirr hν.1 hπ
end FD1D.FiniteKernel
