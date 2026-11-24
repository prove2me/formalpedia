-- Prove2me | solution 1 for FunctorialResolution.EmbeddedResolution.isRadical_biInf_span_singleton
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T11:49:07.714425+00:00
-- url     : https://prove2.me/submissions/84556452-015d-48c4-8448-54009b18b5ef

import Mathlib
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_AlgebraicPreliminaries_SpanSingletonProduct

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open FunctorialResolution FunctorialResolution.EmbeddedResolution
namespace FunctorialResolution.EmbeddedResolution
theorem _root_.solution {R : Type*} [CommRing R] {ι : Type*}
    (f : ι → R) (s : Finset ι)
    (hp : ∀ i ∈ s, (Ideal.span ({f i} : Set R)).IsPrime) :
    (⨅ i ∈ s, Ideal.span ({f i} : Set R)).IsRadical := by
  refine le_iInf fun i => le_iInf fun hi => ?_
  refine le_trans (Ideal.radical_mono ?_) (hp i hi).isRadical
  exact iInf_le_of_le i (iInf_le _ hi)
end FunctorialResolution.EmbeddedResolution
