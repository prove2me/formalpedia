-- Prove2me | solution 1 for FunctorialResolution.EmbeddedResolution.map_logDerivIdealIterate_ker_le_derivIdealIterate_map
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T12:16:04.105845+00:00
-- url     : https://prove2.me/submissions/b0b576d0-245b-452b-95e9-10ab227ddf71

import Mathlib
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_DerivativeIdeal_DerivativeIdeal
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_DerivativeIdeal_LogDerivativeIdeal
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_DerivativeIdeal_DerivationOfSurjective
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_DerivativeIdeal_LogDerivativeIdealQuotient
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_map_logDerivIdeal_ker_le_derivIdeal_map
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_derivIdealIterate_succ
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_derivIdeal_mono
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_logDerivIdealIterate_succ


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
    (hf : Function.Surjective f) (r : ℕ) (J : Ideal S) :
    Ideal.map f.toRingHom (logDerivIdealIterate k (RingHom.ker f.toRingHom) r J)
      ≤ derivIdealIterate k r (Ideal.map f.toRingHom J) := by
  induction r with
  | zero => exact le_rfl
  | succ r ih =>
      rw [logDerivIdealIterate_succ, derivIdealIterate_succ]
      exact (map_logDerivIdeal_ker_le_derivIdeal_map k f hf _).trans (derivIdeal_mono k ih)
end FunctorialResolution.EmbeddedResolution
