-- Prove2me | solution 1 for EdenVerified.p02_one_lt_squaredRadiusEvolution_iff
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T16:06:20.665323+00:00
-- url     : https://prove2.me/submissions/dee51320-3f5e-4311-b60e-cdfa69b9e102

import Definitions.Def_Eden
import Definitions.Def_Eden_Solution
import Theorems.Thm_Eden_one_lt_squaredRadiusEvolution_iff


set_option autoImplicit true
noncomputable section
open Set Filter
open scoped Topology
open Eden
open EdenVerified
namespace EdenVerified
theorem _root_.solution :
    ∀ {t s : ℝ} (ht : 0 ≤ t),
    1 < squaredRadiusEvolution t s ↔ 1 < s :=
  @Eden.one_lt_squaredRadiusEvolution_iff
end EdenVerified
