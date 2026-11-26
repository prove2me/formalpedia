-- Prove2me | solution 1 for EdenVerified.p03_radiusEvolution_zero_time
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T16:07:50.02811+00:00
-- url     : https://prove2.me/submissions/ab2f1d3a-2b55-478f-928b-f44684e6b751

import Definitions.Def_Eden
import Definitions.Def_Eden_Solution
import Theorems.Thm_Eden_radiusEvolution_zero_time
attribute [local simp] Eden.radiusEvolution_zero_time



set_option autoImplicit true
noncomputable section
open Set Filter
open scoped Topology
open Eden
open EdenVerified
namespace EdenVerified
theorem _root_.solution :
    ∀ {r : ℝ} (hr : 0 ≤ r),
    radiusEvolution 0 r = r :=
  @Eden.radiusEvolution_zero_time
end EdenVerified
