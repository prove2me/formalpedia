-- Prove2me | solution 1 for BirkhoffGlobalSection.convex_model_global_frame_extends_over_capping_disk
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-10-03T22:06:04.949315+00:00
-- url     : https://prove2.me/submissions/59e47bd3-bd12-4fdb-adab-7531810ca2d4

import Theorems.Thm_BirkhoffGlobalSection_contact_frame_angle_disk_bundle
open BirkhoffGlobalSection Set Filter SignType
open scoped ContDiff Topology
set_option linter.unusedVariables false


set_option autoImplicit false
set_option maxHeartbeats 800000

theorem solution :
∀ {μ c : ℝ}
    (M : ConvexRegularizationModel μ c) (d : ClosedDiskPoint → Phase)
    (hd : Continuous d) (hs : ∀ z, d z ∈ unitThreeSphere)
    (γ : {z : ClosedDiskPoint // z ∈ closedDiskBoundary} → Phase)
    (hbd : ∀ z, d z.val = γ z),
    ∃ E : ClosedDiskPoint → Fin 2 → Phase,
      (∀ i, Continuous (fun z => E z i)) ∧
      (∀ z i, (d z 0 * E z i 0 + d z 1 * E z i 1 +
        d z 2 * E z i 2 + d z 3 * E z i 3 = 0) ∧ phaseRadialContact (d z) (E z i) = 0) ∧
      (∀ z, let f : Phase → ℝ := fun x => ((gauge M.body x)⁻¹)^2
        fderiv ℝ (fun x => f x * phaseRadialContact x (E z 1)) (d z) (E z 0) -
          fderiv ℝ (fun x => f x * phaseRadialContact x (E z 0)) (d z) (E z 1) = 1) ∧
      (∀ z v, d z 0 * v 0 + d z 1 * v 1 + d z 2 * v 2 + d z 3 * v 3 = 0 →
        phaseRadialContact (d z) v = 0 →
        v = convexModelContactCoordinates M (d z) v 0 • E z 0 +
          convexModelContactCoordinates M (d z) v 1 • E z 1) ∧
      (∀ z (a b : ℝ), a • E z 0 + b • E z 1 = 0 → a = 0 ∧ b = 0) ∧
      (∀ z i, E z.val i = convexModelSymplecticContactFrame M (γ z) i) := by
  exact BirkhoffGlobalSection.contact_frame_angle_disk_bundle.{0}.2.2.2.2.2.2.2.2.2.1
