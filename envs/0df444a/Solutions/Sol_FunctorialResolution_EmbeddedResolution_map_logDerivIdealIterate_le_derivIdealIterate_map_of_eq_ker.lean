-- Prove2me | solution 1 for FunctorialResolution.EmbeddedResolution.map_logDerivIdealIterate_le_derivIdealIterate_map_of_eq_ker
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T12:31:35.459846+00:00
-- url     : https://prove2.me/submissions/65fd29bb-b0a0-45fe-b881-5bd94e340d57

import Mathlib
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_DerivativeIdeal_DerivativeIdeal
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_DerivativeIdeal_LogDerivativeIdeal
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_DerivativeIdeal_DerivationOfSurjective
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_DerivativeIdeal_LogDerivativeIdealQuotient
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_map_logDerivIdealIterate_ker_le_derivIdealIterate_map

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open FunctorialResolution FunctorialResolution.EmbeddedResolution
variable (k : Type*) [CommRing k] {S T : Type*} [CommRing S] [CommRing T]
  [Algebra k S] [Algebra k T]
namespace FunctorialResolution.EmbeddedResolution
theorem _root_.solution (f : S →ₐ[k] T)
    (hf : Function.Surjective f) {P : Ideal S} (hP : P = RingHom.ker f.toRingHom)
    (r : ℕ) (J : Ideal S) :
    Ideal.map f.toRingHom (logDerivIdealIterate k P r J)
      ≤ derivIdealIterate k r (Ideal.map f.toRingHom J) := by
  subst hP
  exact map_logDerivIdealIterate_ker_le_derivIdealIterate_map k f hf r J
end FunctorialResolution.EmbeddedResolution
