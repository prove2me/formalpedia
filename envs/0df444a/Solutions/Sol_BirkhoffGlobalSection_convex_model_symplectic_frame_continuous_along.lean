-- Prove2me | solution 1 for BirkhoffGlobalSection.convex_model_symplectic_frame_continuous_along
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-10-03T22:06:04.387985+00:00
-- url     : https://prove2.me/submissions/e6e2412e-68b7-4c01-afef-ca0d9fbf7151

import Theorems.Thm_BirkhoffGlobalSection_contact_frame_angle_disk_bundle
open BirkhoffGlobalSection Set Filter SignType
open scoped ContDiff Topology
set_option linter.unusedVariables false


set_option autoImplicit false
set_option maxHeartbeats 800000

universe u_convex_model_symplectic_frame_continuous_along

theorem solution :
∀ {A : Type u_convex_model_symplectic_frame_continuous_along} [TopologicalSpace A]
    {μ c : ℝ} (M : ConvexRegularizationModel μ c) (d : A → Phase)
    (hd : Continuous d) (hs : ∀ z, d z ∈ unitThreeSphere) (i : Fin 2),
    Continuous (fun z => convexModelSymplecticContactFrame M (d z) i) := by
  exact BirkhoffGlobalSection.contact_frame_angle_disk_bundle.{u_convex_model_symplectic_frame_continuous_along}.2.2.2.2.2.2.2.2.1
