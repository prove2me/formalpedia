-- Prove2me | solution 1 for EdenVerified.p28_eventually_dimension_zero_of_limiting_radii
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T16:20:53.226501+00:00
-- url     : https://prove2.me/submissions/0a14c338-7592-4a00-968b-98e33fd7fad0

import Definitions.Def_Eden
import Definitions.Def_Eden_Solution
import Theorems.Thm_Eden_eventually_dimension_zero_of_limiting_radii


set_option autoImplicit true
noncomputable section
open Set Filter
open scoped Topology
open Eden
open EdenVerified
namespace EdenVerified
theorem _root_.solution :
    ∀ {c : ℝ} (hc : 4 < c)
    (p : PhaseSpace) (h₁ : limitingSquaredRadius (radiusSq₁ p) = 0)
    (h₂ : limitingSquaredRadius (radiusSq₂ p) = 0),
    ∀ᶠ t in atTop, (∀ i, normalizedLogSingularValues c t p i < 0) ∧
      finiteTimeDimension c t p = 0 :=
  @Eden.eventually_dimension_zero_of_limiting_radii
end EdenVerified
