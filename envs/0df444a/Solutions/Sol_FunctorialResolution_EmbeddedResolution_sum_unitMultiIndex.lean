-- Prove2me | solution 1 for FunctorialResolution.EmbeddedResolution.sum_unitMultiIndex
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T11:51:28.594023+00:00
-- url     : https://prove2.me/submissions/a95b9396-ba55-4b74-b22b-b9b9cccdd5bf

import Mathlib
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_DerivativeIdeal_MultiIndexDerivation
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_unitMultiIndex_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] FunctorialResolution.EmbeddedResolution.unitMultiIndex_apply

set_option autoImplicit false
open FunctorialResolution FunctorialResolution.EmbeddedResolution
variable {k R : Type*} [CommRing k] [CommRing R] [Algebra k R]
namespace FunctorialResolution.EmbeddedResolution
theorem _root_.solution {h : ℕ} (i : Fin h) : ∑ j, unitMultiIndex i j = 1 := by
  simp [unitMultiIndex]
end FunctorialResolution.EmbeddedResolution
