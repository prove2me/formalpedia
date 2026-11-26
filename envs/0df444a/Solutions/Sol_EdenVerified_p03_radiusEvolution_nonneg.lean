-- Prove2me | solution 1 for EdenVerified.p03_radiusEvolution_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T16:08:02.688613+00:00
-- url     : https://prove2.me/submissions/90d5a5a8-29e8-493b-abaa-86a15d1f7543

import Definitions.Def_Eden
import Definitions.Def_Eden_Solution
import Theorems.Thm_Eden_radiusEvolution_nonneg


set_option autoImplicit true
noncomputable section
open Set Filter
open scoped Topology
open Eden
open EdenVerified
namespace EdenVerified
theorem _root_.solution :
    ∀ (t r : ℝ),
    0 ≤ radiusEvolution t r :=
  @Eden.radiusEvolution_nonneg
end EdenVerified
