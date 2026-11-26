-- Prove2me | solution 1 for EdenVerified.p05_evolution_image_attractor
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T16:11:23.068799+00:00
-- url     : https://prove2.me/submissions/e30f45fe-ffb1-404f-8fb4-4efbbdb9ec33

import Definitions.Def_Eden
import Definitions.Def_Eden_Solution
import Theorems.Thm_Eden_evolution_image_attractor


set_option autoImplicit true
noncomputable section
open Set Filter
open scoped Topology
open Eden
open EdenVerified
namespace EdenVerified
theorem _root_.solution :
    ∀ (c : ℝ) {t : ℝ} (ht : 0 ≤ t),
    evolution c t '' attractor = attractor :=
  @Eden.evolution_image_attractor
end EdenVerified
