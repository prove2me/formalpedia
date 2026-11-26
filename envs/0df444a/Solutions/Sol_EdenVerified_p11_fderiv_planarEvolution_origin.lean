-- Prove2me | solution 1 for EdenVerified.p11_fderiv_planarEvolution_origin
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T16:15:15.961205+00:00
-- url     : https://prove2.me/submissions/4a1c0be6-d293-410c-aafe-0652152c822d

import Definitions.Def_Eden
import Definitions.Def_Eden_Solution
import Theorems.Thm_Eden_fderiv_planarEvolution_origin


set_option autoImplicit true
noncomputable section
open Set Filter
open scoped Topology
open Eden
open EdenVerified
namespace EdenVerified
theorem _root_.solution :
    ∀ (Ω : ℝ) {t : ℝ} (ht : 0 ≤ t) (v : PlanarSpace),
    fderiv ℝ (planarEvolution Ω t) 0 v =
      Real.exp (-2 * t) • planarAngularRotation Ω t v :=
  @Eden.fderiv_planarEvolution_origin
end EdenVerified
