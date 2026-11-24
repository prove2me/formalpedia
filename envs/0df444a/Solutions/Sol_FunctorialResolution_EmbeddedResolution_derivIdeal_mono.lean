-- Prove2me | solution 1 for FunctorialResolution.EmbeddedResolution.derivIdeal_mono
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T23:05:28.620545+00:00
-- url     : https://prove2.me/submissions/2cf52a12-fffe-4abb-887a-4ab99144da3c

import Mathlib
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_DerivativeIdeal_DerivativeIdeal
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_le_derivIdeal
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_derivation_apply_mem_derivIdeal
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_derivIdeal_le_iff

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
theorem _root_.solution (k : Type*) [CommRing k] {S : Type*} [CommRing S] [Algebra k S] :
    Monotone (derivIdeal k : Ideal S → Ideal S) := by
  intro I J h
  rw [derivIdeal_le_iff]
  exact ⟨h.trans (le_derivIdeal k J), fun D x hx => derivation_apply_mem_derivIdeal k J D (h hx)⟩
end FunctorialResolution.EmbeddedResolution
