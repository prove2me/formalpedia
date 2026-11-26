-- Prove2me | solution 1 for Eden.volumeDefect_integrand_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T15:12:18.088176+00:00
-- url     : https://prove2.me/submissions/92acaa9d-af10-4b2e-8b7c-b16bf1b2eae3

import Definitions.Def_Eden_VolumeGrowth
import Definitions.Def_Eden_Uniqueness
import Definitions.Def_Eden_VolumeConsequences

set_option autoImplicit true
noncomputable section
open Eden
namespace Eden
theorem _root_.solution (c τ : ℝ) (p : PhaseSpace) :
    0 ≤ (radiusSq₁ (evolution c τ p) - 1) ^ 2 +
      (radiusSq₂ (evolution c τ p) - 1) ^ 2 :=
  add_nonneg (sq_nonneg _) (sq_nonneg _)
end Eden
