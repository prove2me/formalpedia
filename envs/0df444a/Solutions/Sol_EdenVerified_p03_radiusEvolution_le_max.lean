-- Prove2me | solution 1 for EdenVerified.p03_radiusEvolution_le_max
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T16:08:04.902531+00:00
-- url     : https://prove2.me/submissions/ec7388e3-e98f-4b73-b4fd-4b672db473f7

import Definitions.Def_Eden
import Definitions.Def_Eden_Solution
import Theorems.Thm_Eden_radiusEvolution_le_max


set_option autoImplicit true
noncomputable section
open Set Filter
open scoped Topology
open Eden
open EdenVerified
namespace EdenVerified
theorem _root_.solution :
    ∀ {t r : ℝ} (ht : 0 ≤ t) (hr : 0 ≤ r),
    radiusEvolution t r ≤ max r (Real.sqrt 2) :=
  @Eden.radiusEvolution_le_max
end EdenVerified
