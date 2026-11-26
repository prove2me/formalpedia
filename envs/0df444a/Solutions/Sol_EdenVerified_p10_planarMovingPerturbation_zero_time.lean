-- Prove2me | solution 1 for EdenVerified.p10_planarMovingPerturbation_zero_time
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T16:13:48.776825+00:00
-- url     : https://prove2.me/submissions/3fd77b64-269c-401b-ac72-68af513d16b5

import Definitions.Def_Eden
import Definitions.Def_Eden_Solution
import Theorems.Thm_Eden_planarMovingPerturbation_zero_time
attribute [local simp] Eden.planarMovingPerturbation_zero_time



set_option autoImplicit true
noncomputable section
open Set Filter
open scoped Topology
open Eden
open EdenVerified
namespace EdenVerified
theorem _root_.solution :
    ∀ (Ω : ℝ) (p v : PlanarSpace),
    planarMovingPerturbation Ω 0 p v = v :=
  @Eden.planarMovingPerturbation_zero_time
end EdenVerified
