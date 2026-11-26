-- Prove2me | solution 1 for EdenVerified.p17_volumeDefect_integrand_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T16:27:33.583665+00:00
-- url     : https://prove2.me/submissions/36f39927-51e7-44a5-a885-04e5feff0d2f

import Definitions.Def_Eden
import Definitions.Def_Eden_Solution
import Theorems.Thm_Eden_volumeDefect_integrand_nonneg


set_option autoImplicit true
noncomputable section
open Set Filter
open scoped Topology
open Eden
open EdenVerified
namespace EdenVerified
theorem _root_.solution :
    ∀ (c τ : ℝ) (p : PhaseSpace),
    0 ≤ (radiusSq₁ (evolution c τ p) - 1) ^ 2 +
      (radiusSq₂ (evolution c τ p) - 1) ^ 2 :=
  @Eden.volumeDefect_integrand_nonneg
end EdenVerified
