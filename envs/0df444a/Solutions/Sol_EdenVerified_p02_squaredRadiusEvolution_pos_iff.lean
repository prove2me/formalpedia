-- Prove2me | solution 1 for EdenVerified.p02_squaredRadiusEvolution_pos_iff
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T16:06:09.83642+00:00
-- url     : https://prove2.me/submissions/7bbd5e47-b0b4-40f4-8e71-26a292587059

import Definitions.Def_Eden
import Definitions.Def_Eden_Solution
import Theorems.Thm_Eden_squaredRadiusEvolution_pos_iff


set_option autoImplicit true
noncomputable section
open Set Filter
open scoped Topology
open Eden
open EdenVerified
namespace EdenVerified
theorem _root_.solution :
    ∀ {t s : ℝ} (ht : 0 ≤ t),
    0 < squaredRadiusEvolution t s ↔ 0 < s :=
  @Eden.squaredRadiusEvolution_pos_iff
end EdenVerified
