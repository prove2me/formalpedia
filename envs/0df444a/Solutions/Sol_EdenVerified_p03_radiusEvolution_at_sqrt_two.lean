-- Prove2me | solution 1 for EdenVerified.p03_radiusEvolution_at_sqrt_two
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T16:08:35.821935+00:00
-- url     : https://prove2.me/submissions/2e6167ba-1f5d-470c-bbac-367a11f7ee43

import Definitions.Def_Eden
import Definitions.Def_Eden_Solution
import Theorems.Thm_Eden_radiusEvolution_at_sqrt_two
attribute [local simp] Eden.radiusEvolution_at_sqrt_two



set_option autoImplicit true
noncomputable section
open Set Filter
open scoped Topology
open Eden
open EdenVerified
namespace EdenVerified
theorem _root_.solution :
    ∀ (t : ℝ),
    radiusEvolution t (Real.sqrt 2) = Real.sqrt 2 :=
  @Eden.radiusEvolution_at_sqrt_two
end EdenVerified
