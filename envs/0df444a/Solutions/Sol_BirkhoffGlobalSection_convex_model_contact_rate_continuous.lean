-- Prove2me | solution 1 for BirkhoffGlobalSection.convex_model_contact_rate_continuous
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-28T14:19:21.058873+00:00
-- url     : https://prove2.me/submissions/d87567e8-f521-4b30-b9c0-58129a0f9eb4

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

import Theorems.Thm_BirkhoffGlobalSection_hamiltonian_radial_contact_continuousAt
open Set
open scoped Topology ContDiff

set_option autoImplicit false
set_option maxHeartbeats 800000

theorem solution {μ c : ℝ}
    (M : BirkhoffGlobalSection.ConvexRegularizationModel μ c) :
    Continuous (fun s : BirkhoffGlobalSection.ConvexModelState M =>
      BirkhoffGlobalSection.phaseRadialContact s
        (BirkhoffGlobalSection.hamiltonianVectorField M.modelHamiltonian s)) := by
  rw [continuous_iff_continuousAt]
  intro s
  have hs : (s : BirkhoffGlobalSection.Phase) ∈ M.target := by
    have hy : (s : BirkhoffGlobalSection.Phase) ∈ M.toModel '' BirkhoffGlobalSection.leftEnergyComponent μ c := by
      rw [M.image_frontier]; exact s.property
    obtain ⟨x, hx, hxy⟩ := hy
    rw [← hxy]
    exact M.toModel_mapsTo (M.contains_component hx)
  have h := BirkhoffGlobalSection.hamiltonian_radial_contact_continuousAt M.modelHamiltonian s
    (M.model_smooth.contDiffAt (M.target_open.mem_nhds hs))
  exact h.comp continuous_subtype_val.continuousAt
