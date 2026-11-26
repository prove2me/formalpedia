-- Prove2me | solution 1 for EdenVerified.p02_strictMono_squaredRadiusEvolution
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T16:05:59.341975+00:00
-- url     : https://prove2.me/submissions/e365be91-2281-4e02-9a28-ffdd8c5076a4

import Definitions.Def_Eden
import Definitions.Def_Eden_Solution
import Theorems.Thm_Eden_strictMono_squaredRadiusEvolution


set_option autoImplicit true
noncomputable section
open Set Filter
open scoped Topology
open Eden
open EdenVerified
namespace EdenVerified
theorem _root_.solution :
    ∀ {t : ℝ} (ht : 0 ≤ t),
    StrictMono (squaredRadiusEvolution t) :=
  @Eden.strictMono_squaredRadiusEvolution
end EdenVerified
