-- Prove2me | solution 1 for BirkhoffGlobalSection.radial_normalize_regular
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-10-03T21:16:45.131456+00:00
-- url     : https://prove2.me/submissions/738d1bff-66a3-4850-bd71-314a05c07a2a

import Theorems.Thm_BirkhoffGlobalSection_smooth_sphere_reeb_bundle
open BirkhoffGlobalSection Set Filter SignType
open scoped ContDiff Topology
set_option linter.unusedVariables false


set_option autoImplicit false
set_option maxHeartbeats 800000

theorem solution :
∀ (x : Phase) (hx : 0 < zNormSq x + wNormSq x),
    ContDiffAt ℝ ∞ radialNormalize x ∧ radialNormalize x ∈ unitThreeSphere := by
  exact BirkhoffGlobalSection.smooth_sphere_reeb_bundle.1
