-- Prove2me | solution 1 for FunctorialResolution.EmbeddedResolution.topologicalKrullDim_spec_lt_top
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T13:41:41.33493+00:00
-- url     : https://prove2.me/submissions/d9d647f1-0987-4e9d-abd9-a6341c7b045d

import Mathlib
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_IdealPrincipalization_KrullDimClosedSubset
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_IdealPrincipalization_MarkedBlowupSequence_IdealBlowupSequence
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_IdealPrincipalization_MarkedBlowupSequence_MarkedSequenceOfBlowups
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_BlowupUniversalProperty
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_ResolutionOfSingularities
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_IdealPrincipalization_FiniteKrullDim
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_topologicalKrullDim_primeSpectrum_lt_top

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
theorem _root_.solution (k : Type u) [Field k] (R : CommRingCat.{v})
    [Algebra k R] [Algebra.FiniteType k R] : topologicalKrullDim ↥(Spec R) < ⊤ :=
  topologicalKrullDim_primeSpectrum_lt_top k R
end FunctorialResolution.EmbeddedResolution
