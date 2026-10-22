-- Prove2me | solution 1 for BirkhoffGlobalSection.radial_scale_contDiffAt
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-10-03T21:16:46.96991+00:00
-- url     : https://prove2.me/submissions/670ebc42-7859-440a-9585-1ffad376a23b

import Theorems.Thm_BirkhoffGlobalSection_smooth_sphere_reeb_bundle
open BirkhoffGlobalSection Set Filter SignType
open scoped ContDiff Topology
set_option linter.unusedVariables false


set_option autoImplicit false
set_option maxHeartbeats 800000

theorem solution :
∀ (a : Phase → ℝ) (u : Phase) (hu : u ≠ 0)
    (hG : ContDiffAt ℝ ∞ (fun x : Phase => a x • x) u),
    ContDiffAt ℝ ∞ a u := by
  exact BirkhoffGlobalSection.smooth_sphere_reeb_bundle.2.2.2.1
