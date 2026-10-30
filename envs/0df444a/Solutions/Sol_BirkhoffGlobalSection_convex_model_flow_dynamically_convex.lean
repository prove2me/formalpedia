-- Prove2me | solution 1 for BirkhoffGlobalSection.convex_model_flow_dynamically_convex
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-10-03T19:34:50.26689+00:00
-- url     : https://prove2.me/submissions/745d5a38-8584-46f9-9ee3-6d788f5fb26e

import Theorems.Thm_BirkhoffGlobalSection_dynamically_convex_on_strictly_convex_star_shaped_points
import Theorems.Thm_BirkhoffGlobalSection_convex_model_boundary_contact_positive

open BirkhoffGlobalSection

/-- `α_y(X_H(y)) = ½ dH(y) y` for the radial contact form `α_y(v) = -ω(y, v)/2`. -/
theorem radialContact_ham_eq (F : Phase → ℝ) (y : Phase) :
    phaseRadialContact y (hamiltonianVectorField F y) = fderiv ℝ F y y / 2 := by
  have hy : y = ∑ i, y i • coordinateVector i := by
    ext i; simp [coordinateVector, Finset.sum_apply, Pi.smul_apply]
  have hL : fderiv ℝ F y y = ∑ i, y i * fderiv ℝ F y (coordinateVector i) := by
    set L := fderiv ℝ F y
    conv_lhs => rw [hy]
    simp [map_sum, map_smul]
  rw [hL]
  simp [phaseRadialContact, phaseSymplecticForm, hamiltonianVectorField, partialDerivative,
    Fin.sum_univ_four]
  ring

theorem solution {μ c : ℝ}
    (M : ConvexRegularizationModel μ c) :
    IsDynamicallyConvexOn M.modelHamiltonian (frontier M.body) := by
  intro x T hx
  apply dynamically_convex_on_strictly_convex_star_shaped_points M.modelHamiltonian x T
  refine ⟨hx.1, fun t => ?_, hx.2.2.1, hx.2.2.2⟩
  have hy := hx.2.1 t
  refine ⟨⟨fun s hs => ?_, fun s hs v hv hker => ?_⟩, ?_⟩
  · rw [Set.mem_singleton_iff] at hs; subst hs
    exact M.model_hessian.1 _ hy
  · rw [Set.mem_singleton_iff] at hs; subst hs
    exact M.model_hessian.2 _ hy v hv hker
  · have h := convex_model_boundary_contact_positive M (x t) hy
    rw [radialContact_ham_eq] at h
    linarith
