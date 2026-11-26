-- Prove2me | solution 1 for EdenVerified.p17_continuousOn_volumeDefect_integrand
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T16:27:28.131511+00:00
-- url     : https://prove2.me/submissions/f343b524-8fdd-4799-96d3-df3901ba6906

import Definitions.Def_Eden
import Definitions.Def_Eden_Solution
import Theorems.Thm_Eden_continuousOn_volumeDefect_integrand


set_option autoImplicit true
noncomputable section
open Set Filter
open scoped Topology
open Eden
open EdenVerified
namespace EdenVerified
theorem _root_.solution :
    ∀ (c : ℝ) (p : PhaseSpace),
    ContinuousOn (fun τ => (radiusSq₁ (evolution c τ p) - 1) ^ 2 +
      (radiusSq₂ (evolution c τ p) - 1) ^ 2) (Set.Ici 0) :=
  @Eden.continuousOn_volumeDefect_integrand
end EdenVerified
