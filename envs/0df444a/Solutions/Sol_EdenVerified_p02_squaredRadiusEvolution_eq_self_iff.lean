-- Prove2me | solution 1 for EdenVerified.p02_squaredRadiusEvolution_eq_self_iff
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T16:07:19.78291+00:00
-- url     : https://prove2.me/submissions/7e6ad800-e8a3-46ff-8913-ec0fbe557594

import Definitions.Def_Eden
import Definitions.Def_Eden_Solution
import Theorems.Thm_Eden_squaredRadiusEvolution_eq_self_iff


set_option autoImplicit true
noncomputable section
open Set Filter
open scoped Topology
open Eden
open EdenVerified
namespace EdenVerified
theorem _root_.solution :
    ∀ {t s : ℝ} (ht : 0 < t),
    squaredRadiusEvolution t s = s ↔ s = 0 ∨ s = 1 ∨ s = 2 :=
  @Eden.squaredRadiusEvolution_eq_self_iff
end EdenVerified
