-- Prove2me | solution 1 for FunctorialResolution.EmbeddedResolution.imageIdealSheaf_comp
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T23:44:48.955812+00:00
-- url     : https://prove2.me/submissions/c2b9573d-ff61-4dc8-bed7-aaf22fb034d9

import Mathlib
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_Blowup_StrictTransform
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_BlowupUniversalProperty
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_ResolutionOfSingularities
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_IteratedBlowups_BlowupSequenceRelations
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_map_eq_imageIdealSheaf

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
theorem _root_.solution {W A B : Scheme.{u}} (g : W ⟶ A) (w : A ⟶ B) (I : W.IdealSheafData) :
    imageIdealSheaf (g ≫ w) I = imageIdealSheaf w (imageIdealSheaf g I) := by
  simp only [← map_eq_imageIdealSheaf, Scheme.IdealSheafData.map_comp]
end FunctorialResolution.EmbeddedResolution
