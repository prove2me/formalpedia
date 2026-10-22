-- Prove2me | solution 1 for BirkhoffGlobalSection.weighted_sphere_reeb_exists_unique
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-10-03T21:13:21.315979+00:00
-- url     : https://prove2.me/submissions/29353e65-d5e4-4e4c-bf11-9b81f4c86b37

import Theorems.Thm_BirkhoffGlobalSection_weighted_reeb_bundle
open BirkhoffGlobalSection Set Filter SignType
open scoped ContDiff Topology
set_option linter.unusedVariables false


set_option autoImplicit false
set_option maxHeartbeats 800000

theorem solution :
∀ (f : Phase → ℝ) (u : Phase)
    (hu : u ∈ unitThreeSphere) (hf : 0 < f u) (hdf : DifferentiableAt ℝ f u),
    ∃! R : Phase,
      u 0 * R 0 + u 1 * R 1 + u 2 * R 2 + u 3 * R 3 = 0 ∧
      f u * phaseRadialContact u R = 1 ∧
      (∀ w : Phase,
        u 0 * w 0 + u 1 * w 1 + u 2 * w 2 + u 3 * w 3 = 0 →
        fderiv ℝ (fun x => f x * phaseRadialContact x w) u R -
          fderiv ℝ (fun x => f x * phaseRadialContact x R) u w = 0) := by
  exact BirkhoffGlobalSection.weighted_reeb_bundle.2.1
