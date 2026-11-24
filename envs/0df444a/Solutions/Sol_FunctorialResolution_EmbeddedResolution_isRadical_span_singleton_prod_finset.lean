-- Prove2me | solution 1 for FunctorialResolution.EmbeddedResolution.isRadical_span_singleton_prod_finset
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T12:03:54.797791+00:00
-- url     : https://prove2.me/submissions/6abeb33a-cc3c-4204-9bc4-3eee04d6ecb9

import Mathlib
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_AlgebraicPreliminaries_SpanSingletonProduct
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_span_singleton_prod_eq_biInf
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_isRadical_biInf_span_singleton

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
    [DecidableEq ι]
    (f : ι → R) (s : Finset ι)
    (hp : ∀ i ∈ s, (Ideal.span ({f i} : Set R)).IsPrime)
    (hdvd : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → f j ∉ Ideal.span ({f i} : Set R)) :
    (Ideal.span ({∏ i ∈ s, f i} : Set R)).IsRadical := by
  rw [span_singleton_prod_eq_biInf f s hp hdvd]
  exact isRadical_biInf_span_singleton f s hp
end FunctorialResolution.EmbeddedResolution
