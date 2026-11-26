-- Prove2me | solution 1 for EdenVerified.p02_radiusEvolution_mono
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T16:06:06.518125+00:00
-- url     : https://prove2.me/submissions/36dc5db1-2461-472b-bb60-314596df6eab

import Definitions.Def_Eden
import Definitions.Def_Eden_Solution
import Theorems.Thm_Eden_radiusEvolution_mono


set_option autoImplicit true
noncomputable section
open Set Filter
open scoped Topology
open Eden
open EdenVerified
namespace EdenVerified
theorem _root_.solution :
    ∀ {t r R : ℝ} (ht : 0 ≤ t) (hr : 0 ≤ r) (hrR : r ≤ R),
    radiusEvolution t r ≤ radiusEvolution t R :=
  @Eden.radiusEvolution_mono
end EdenVerified
