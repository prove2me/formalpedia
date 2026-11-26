-- Prove2me | solution 1 for EdenVerified.p02_squaredRadiusEvolution_lt_two_iff
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T16:06:39.9188+00:00
-- url     : https://prove2.me/submissions/d3f4f227-2a3a-42e5-b7b4-13cf87c0898d

import Definitions.Def_Eden
import Definitions.Def_Eden_Solution
import Theorems.Thm_Eden_squaredRadiusEvolution_lt_two_iff


set_option autoImplicit true
noncomputable section
open Set Filter
open scoped Topology
open Eden
open EdenVerified
namespace EdenVerified
theorem _root_.solution :
    ∀ {t s : ℝ} (ht : 0 ≤ t),
    squaredRadiusEvolution t s < 2 ↔ s < 2 :=
  @Eden.squaredRadiusEvolution_lt_two_iff
end EdenVerified
