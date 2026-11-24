-- Prove2me | solution 1 for FunctorialResolution.EmbeddedResolution.truncatedSeries_length_one
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T00:04:51.179131+00:00
-- url     : https://prove2.me/submissions/b7c33bce-d786-4308-91f3-26229f0a6c06

import Mathlib
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_DerivativeIdeal_DerivativeIdeal
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_DerivativeIdeal_TaylorExpansion
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_DerivativeIdeal_TaylorExpansionComparison
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_TaylorExpansion_truncatedSeriesRingHom_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] FunctorialResolution.EmbeddedResolution.TaylorExpansion.truncatedSeriesRingHom_apply



set_option autoImplicit false
open FunctorialResolution FunctorialResolution.EmbeddedResolution
variable {A R S : Type*} [CommRing A] [CommRing R] [CommRing S] [Algebra A R] [Algebra ℚ S]
namespace FunctorialResolution.EmbeddedResolution
theorem _root_.solution (σ : R →+* S) (D : Derivation A R R) (β : S) (f : R) :
    TaylorExpansion.truncatedSeries σ D β 1 f = σ f := by
  simp [TaylorExpansion.truncatedSeries_apply]
end FunctorialResolution.EmbeddedResolution
