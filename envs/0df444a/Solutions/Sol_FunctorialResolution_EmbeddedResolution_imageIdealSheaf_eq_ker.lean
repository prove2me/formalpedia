-- Prove2me | solution 1 for FunctorialResolution.EmbeddedResolution.imageIdealSheaf_eq_ker
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T23:04:37.53794+00:00
-- url     : https://prove2.me/submissions/416298e6-92e1-4922-a5d5-07061304d47b

import Mathlib
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_Blowup_StrictTransform
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_BlowupUniversalProperty
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_ResolutionOfSingularities
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_IteratedBlowups_BlowupSequenceRelations

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
universe u
open CategoryTheory AlgebraicGeometry
noncomputable section
open FunctorialResolution FunctorialResolution.EmbeddedResolution
namespace FunctorialResolution.EmbeddedResolution
theorem _root_.solution {S X : Scheme.{u}} (σ : S ⟶ X) (I : S.IdealSheafData) :
    imageIdealSheaf σ I = (I.subschemeι ≫ σ).ker := rfl
end FunctorialResolution.EmbeddedResolution
