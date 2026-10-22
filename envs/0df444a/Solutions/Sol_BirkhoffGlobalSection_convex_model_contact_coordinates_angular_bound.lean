-- Prove2me | solution 1 for BirkhoffGlobalSection.convex_model_contact_coordinates_angular_bound
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-10-03T22:06:03.815572+00:00
-- url     : https://prove2.me/submissions/dfae54b5-c30b-41e8-a243-3da6b9574252

import Theorems.Thm_BirkhoffGlobalSection_contact_frame_angle_disk_bundle
open BirkhoffGlobalSection Set Filter SignType
open scoped ContDiff Topology
set_option linter.unusedVariables false


set_option autoImplicit false
set_option maxHeartbeats 800000

theorem solution :
∀ {μ c : ℝ}
    (M : ConvexRegularizationModel μ c) (q v : ℝ → Phase) (T B : ℝ)
    (hq : ∀ t, q t ∈ unitThreeSphere)
    (hbound : ∀ θ : ℝ → ℝ, Continuous θ →
      (∀ t, ∃ r : ℝ, 0 < r ∧
        transverseFrameCoordinates
          (TangentialHessian.grad M.modelHamiltonian ((gauge M.body (q t))⁻¹ • q t))
          (fderiv ℝ (fun x : Phase => (gauge M.body x)⁻¹ • x) (q t) (v t)) =
            ![r * Real.cos (θ t), r * Real.sin (θ t)]) → B < θ T - θ 0),
    ∀ θ : ℝ → ℝ, Continuous θ →
      (∀ t, ∃ r : ℝ, 0 < r ∧ convexModelContactCoordinates M (q t) (v t) =
        ![r * Real.cos (θ t), r * Real.sin (θ t)]) → B < θ T - θ 0 := by
  exact BirkhoffGlobalSection.contact_frame_angle_disk_bundle.{0}.2.2.2.2.2.2.2.1
