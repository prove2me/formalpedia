-- Prove2me | solution 1 for CohnElkies.tendsto_lowerPoissonEndpointExpectation
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:24.652437+00:00
-- url     : https://prove2.me/submissions/afd53fc5-1c67-483f-9483-9a1390342605

import Mathlib
import Definitions.Def_SpherePacking
import Theorems.Thm_CohnElkies_lowerEndpointPhase_continuous
import Theorems.Thm_CohnElkies_stripPoissonExponentialMajorant_mul_lowerEndpointPhase_integrable
import Theorems.Thm_CohnElkies_tendsto_integral_stripNormalizedPoissonKernel_mul

set_option autoImplicit true
open CohnElkies
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 800000
noncomputable section
open Filter MeasureTheory Set
open scoped Interval Topology
namespace CohnElkies
theorem _root_.solution :
    Tendsto lowerPoissonEndpointExpectation (𝓝[<] 1)
      (𝓝 limitingPoissonEndpointExpectation) := by
  exact tendsto_integral_stripNormalizedPoissonKernel_mul
    lowerEndpointPhase
    lowerEndpointPhase_continuous.aestronglyMeasurable
    stripPoissonExponentialMajorant_mul_lowerEndpointPhase_integrable
end CohnElkies
