-- Prove2me | solution 1 for BirkhoffGlobalSection.convex_model_contact_clock
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-28T14:19:39.32909+00:00
-- url     : https://prove2.me/submissions/2ca32759-03a1-4c69-80d8-3b11d54ce32f

import Theorems.Thm_BirkhoffGlobalSection_convex_model_boundary_contact_positive
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Topology.Order.Compact
import Mathlib.Order.Hom.Set
import Mathlib.Analysis.Calculus.Deriv.Inverse
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Analysis.Calculus.MeanValue
import Theorems.Thm_BirkhoffGlobalSection_hamiltonian_radial_characteristic_normalization

import Theorems.Thm_BirkhoffGlobalSection_compact_trajectory_positive_clock
import Theorems.Thm_BirkhoffGlobalSection_hamiltonian_radial_contact_continuousAt
open Set
open scoped Topology ContDiff

set_option autoImplicit false
set_option maxHeartbeats 800000

theorem solution {μ c : ℝ}
    (M : BirkhoffGlobalSection.ConvexRegularizationModel μ c)
    {φ : Flow ℝ (BirkhoffGlobalSection.LeftEnergyState μ c)}
    (D : BirkhoffGlobalSection.ConvexModelDynamics M φ)
    (hcontact : ∀ y ∈ frontier M.body,
      0 < BirkhoffGlobalSection.phaseRadialContact y
        (BirkhoffGlobalSection.hamiltonianVectorField M.modelHamiltonian y))
    (s : BirkhoffGlobalSection.ConvexModelState M) :
    ∃ clock : ℝ ≃o ℝ,
      clock 0 = 0 ∧
      (∀ t, HasDerivAt clock
        (BirkhoffGlobalSection.phaseRadialContact (D.flow t s)
          (BirkhoffGlobalSection.hamiltonianVectorField M.modelHamiltonian (D.flow t s))) t) ∧
      (∀ t, clock t = ∫ v in (0 : ℝ)..t,
        BirkhoffGlobalSection.phaseRadialContact (D.flow v s)
          (BirkhoffGlobalSection.hamiltonianVectorField M.modelHamiltonian (D.flow v s))) := by
  have hK : IsCompact (frontier M.body) :=
    M.body_compact.of_isClosed_subset isClosed_frontier
      (frontier_subset_closure.trans M.body_compact.isClosed.closure_subset)
  have hr : ContinuousOn (fun x => BirkhoffGlobalSection.phaseRadialContact x
      (BirkhoffGlobalSection.hamiltonianVectorField M.modelHamiltonian x)) (frontier M.body) := by
    intro y hy
    have hs : y ∈ M.target := by
      have hy' : y ∈ M.toModel '' BirkhoffGlobalSection.leftEnergyComponent μ c := by
        rw [M.image_frontier]; exact hy
      obtain ⟨x, hx, hxy⟩ := hy'
      rw [← hxy]
      exact M.toModel_mapsTo (M.contains_component hx)
    exact (BirkhoffGlobalSection.hamiltonian_radial_contact_continuousAt M.modelHamiltonian y
      (M.model_smooth.contDiffAt (M.target_open.mem_nhds hs))).continuousWithinAt
  have hy : Continuous (fun t : ℝ => ((D.flow t s : BirkhoffGlobalSection.ConvexModelState M) :
      BirkhoffGlobalSection.Phase)) :=
    continuous_subtype_val.comp (D.flow.continuous continuous_id continuous_const)
  exact BirkhoffGlobalSection.compact_trajectory_positive_clock (frontier M.body) hK _ hr
    hcontact _ hy (fun t => (D.flow t s).property)
