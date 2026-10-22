-- Prove2me | solution 1 for BirkhoffGlobalSection.radial_normalize_unit
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-10-03T21:16:45.73552+00:00
-- url     : https://prove2.me/submissions/e0db0434-ae75-4250-925d-bd44bf9ee36a

import Theorems.Thm_BirkhoffGlobalSection_smooth_sphere_reeb_bundle
open BirkhoffGlobalSection Set Filter SignType
open scoped ContDiff Topology
set_option linter.unusedVariables false


set_option autoImplicit false
set_option maxHeartbeats 800000

theorem solution :
∀ (u : Phase) (hu : u ∈ unitThreeSphere),
    radialNormalize u = u := by
  exact BirkhoffGlobalSection.smooth_sphere_reeb_bundle.2.1
