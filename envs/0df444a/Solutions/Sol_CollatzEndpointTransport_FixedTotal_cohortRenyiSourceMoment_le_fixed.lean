-- Prove2me | solution 1 for CollatzEndpointTransport.FixedTotal.cohortRenyiSourceMoment_le_fixed
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T09:40:18.391566+00:00
-- url     : https://prove2.me/submissions/e94eb900-5d49-48ed-9886-35d58d8fe3ab

import Definitions.Def_CollatzEndpointTransport_Linear_CentralRenyiReverse
import Definitions.Def_CollatzEndpointTransport_Linear_FiniteFiberMixture
import Definitions.Def_CollatzEndpointTransport_Linear_FixedTotalActualEndpointMoment
import Definitions.Def_CollatzEndpointTransport_Common_TerrasPrefixEvents
import Definitions.Def_CollatzEndpointTransport_Linear_CentralRenyiShell
import Theorems.Thm_CollatzEndpointTransport_FixedTotal_cohortRenyiSourceMoment_eq_fixed

set_option autoImplicit false
open CollatzEndpointTransport
open CollatzEndpointTransport.FixedTotal
open Nat Finset
open scoped Real
noncomputable section
attribute [local instance] CollatzEndpointTransport.FixedTotal.centralEndpointCompositionDecidableEq
namespace CollatzEndpointTransport.FixedTotal
theorem _root_.solution
    (M : ℕ) (u : Fin M) (s : ℕ) {theta : ℝ}
    (_htheta : 0 ≤ theta) :
    cohortRenyiSourceMoment M u s theta ≤
      fixedRenyiNumerator (M - (u : ℕ)) s theta :=
  (cohortRenyiSourceMoment_eq_fixed M u s theta).le
end CollatzEndpointTransport.FixedTotal
