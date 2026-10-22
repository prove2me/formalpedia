-- Prove2me | solution 1 for BirkhoffGlobalSection.convex_model_boundary_contact_positive
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-10-02T00:33:14.844972+00:00
-- url     : https://prove2.me/submissions/09dc8d3a-fc8f-4d1d-b6b1-6d617eeac30e

import Theorems.Thm_ConvexAnalysis_convex_frontier_radial_derivative_positive
import Definitions.Def_BirkhoffGlobalSection_TransverseHopf

open BirkhoffGlobalSection ConvexAnalysis Filter Set
open scoped ContDiff Topology

private theorem convex_model_radial_derivative_positive {μ c : ℝ}
    (M : ConvexRegularizationModel μ c) :
    ∀ y ∈ frontier M.body, 0 < fderiv ℝ M.modelHamiltonian y y := by
  intro y hy
  have hytarget : y ∈ M.target := by
    have hyimage : y ∈ M.toModel '' leftEnergyComponent μ c := by
      rw [M.image_frontier]
      exact hy
    obtain ⟨s, hs, rfl⟩ := hyimage
    exact M.toModel_mapsTo (M.contains_component hs)
  exact convex_frontier_radial_derivative_positive M.body M.body_compact M.body_convex
    M.origin_interior M.modelHamiltonian M.model_zero y hy
    (M.model_smooth.contDiffAt (M.target_open.mem_nhds hytarget)) (M.model_regular y hy)
    (M.model_hessian.2 y hy)

private theorem boundary_pairing_coordinate_expansion (L : Phase →L[ℝ] ℝ) (v : Phase) :
    L v = v 0 * L (coordinateVector 0) + v 1 * L (coordinateVector 1) +
      v 2 * L (coordinateVector 2) + v 3 * L (coordinateVector 3) := by
  have hv : v = v 0 • coordinateVector 0 + v 1 • coordinateVector 1 +
      v 2 • coordinateVector 2 + v 3 • coordinateVector 3 := by
    ext i
    fin_cases i <;> simp [coordinateVector]
  calc
    L v = L (v 0 • coordinateVector 0 + v 1 • coordinateVector 1 +
      v 2 • coordinateVector 2 + v 3 • coordinateVector 3) := congrArg L hv
    _ = _ := by simp

theorem solution {μ c : ℝ}
    (M : ConvexRegularizationModel μ c) :
    ∀ y ∈ frontier M.body,
      0 < phaseRadialContact y (hamiltonianVectorField M.modelHamiltonian y) := by
  intro y hy
  have hpair : phaseRadialContact y (hamiltonianVectorField M.modelHamiltonian y) =
      fderiv ℝ M.modelHamiltonian y y / 2 := by
    rw [boundary_pairing_coordinate_expansion (fderiv ℝ M.modelHamiltonian y) y]
    simp [phaseRadialContact, phaseSymplecticForm, hamiltonianVectorField, partialDerivative]
    ring
  rw [hpair]
  exact div_pos (convex_model_radial_derivative_positive M y hy) (by norm_num)
