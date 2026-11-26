-- Prove2me | solution 1 for EdenVerified.p02_squaredRadiusEvolution_lt_one_iff
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T16:06:10.685555+00:00
-- url     : https://prove2.me/submissions/58e63550-8cbc-4c8a-9ad8-264168b51e65

import Definitions.Def_Eden
import Definitions.Def_Eden_Solution
import Theorems.Thm_Eden_squaredRadiusEvolution_lt_one_iff


set_option autoImplicit true
noncomputable section
open Set Filter
open scoped Topology
open Eden
open EdenVerified
namespace EdenVerified
theorem _root_.solution :
    ∀ {t s : ℝ} (ht : 0 ≤ t),
    squaredRadiusEvolution t s < 1 ↔ s < 1 :=
  @Eden.squaredRadiusEvolution_lt_one_iff
end EdenVerified
