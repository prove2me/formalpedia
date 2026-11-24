-- Prove2me | solution 1 for FunctorialResolution.EmbeddedResolution.restrictIdeal_eq_comap_homOfLE_restrictIdeal
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T23:42:08.75779+00:00
-- url     : https://prove2.me/submissions/40fb10a5-db6d-4734-ae1c-e845236d4f8f

import Mathlib
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_BlowupUniversalProperty
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_ResolutionOfSingularities
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_EtaleCoordinates_StrictNormalCrossings

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry TopologicalSpace
noncomputable section
open FunctorialResolution FunctorialResolution.EmbeddedResolution
namespace FunctorialResolution.EmbeddedResolution
theorem _root_.solution {X : Scheme.{u}} (I : X.IdealSheafData)
    {U V : X.Opens} (h : V ≤ U) :
    restrictIdeal I V = (restrictIdeal I U).comap (X.homOfLE h) := by
  have hcomp : X.homOfLE h ≫ U.ι = V.ι := by simp
  show I.comap V.ι = (I.comap U.ι).comap (X.homOfLE h)
  rw [← Scheme.IdealSheafData.comap_comp, hcomp]
end FunctorialResolution.EmbeddedResolution
