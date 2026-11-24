-- Prove2me | solution 1 for FunctorialResolution.EmbeddedResolution.derivationOfSurjective_apply
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T11:47:33.131802+00:00
-- url     : https://prove2.me/submissions/089e3fd0-fe23-45c4-ae4c-e808679f7a29

import Mathlib
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_DerivativeIdeal_DerivationOfSurjective

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open FunctorialResolution FunctorialResolution.EmbeddedResolution
variable {k S T : Type*} [CommRing k] [CommRing S] [CommRing T]
  [Algebra k S] [Algebra k T]
namespace FunctorialResolution.EmbeddedResolution
theorem _root_.solution (f : S →ₐ[k] T) (hf : Function.Surjective f)
    (D : Derivation k S S)
    (hD : ∀ s ∈ RingHom.ker f.toRingHom, D s ∈ RingHom.ker f.toRingHom) (s : S) :
    derivationOfSurjective f hf D hD (f s) = f (D s) :=
  derivationOfSurjectiveFun_apply f hf D hD s
end FunctorialResolution.EmbeddedResolution
