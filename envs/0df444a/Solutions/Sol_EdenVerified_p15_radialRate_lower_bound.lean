-- Prove2me | solution 1 for EdenVerified.p15_radialRate_lower_bound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T16:25:21.668603+00:00
-- url     : https://prove2.me/submissions/f2fbc796-bdf4-44c3-9e23-f1c9c257e784

import Definitions.Def_Eden
import Definitions.Def_Eden_Solution
import Theorems.Thm_Eden_radialRate_lower_bound


set_option autoImplicit true
noncomputable section
open Set Filter
open scoped Topology
open Eden
open EdenVerified
namespace EdenVerified
theorem _root_.solution :
    ∀ {s : ℝ} (hs₀ : 0 ≤ s) (hs₂ : s ≤ 2),
    -4 ≤ radialRate s :=
  @Eden.radialRate_lower_bound
end EdenVerified
