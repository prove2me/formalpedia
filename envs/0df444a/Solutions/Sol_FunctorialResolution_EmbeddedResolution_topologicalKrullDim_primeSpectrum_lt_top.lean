-- Prove2me | solution 1 for FunctorialResolution.EmbeddedResolution.topologicalKrullDim_primeSpectrum_lt_top
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T13:24:13.407685+00:00
-- url     : https://prove2.me/submissions/a87b8ecd-67ff-4e10-aa6f-6fbf8da68b54

import Mathlib
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_IdealPrincipalization_KrullDimClosedSubset
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_IdealPrincipalization_MarkedBlowupSequence_IdealBlowupSequence
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_IdealPrincipalization_MarkedBlowupSequence_MarkedSequenceOfBlowups
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_BlowupUniversalProperty
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_ResolutionOfSingularities
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_IdealPrincipalization_FiniteKrullDim
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_ringKrullDim_lt_top_of_finiteType

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
universe u v
open TopologicalSpace AlgebraicGeometry
open FunctorialResolution FunctorialResolution.EmbeddedResolution
namespace FunctorialResolution.EmbeddedResolution
theorem _root_.solution (k : Type u) [Field k] (A : Type v) [CommRing A]
    [Algebra k A] [Algebra.FiniteType k A] : topologicalKrullDim (PrimeSpectrum A) < ⊤ := by
  rw [PrimeSpectrum.topologicalKrullDim_eq_ringKrullDim]
  exact ringKrullDim_lt_top_of_finiteType k A
end FunctorialResolution.EmbeddedResolution
