-- Prove2me | solution 1 for FunctorialResolution.EmbeddedResolution.restrictIdeal_comap_eq_comap_resLE_restrictIdeal
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T17:24:14.145371+00:00
-- url     : https://prove2.me/submissions/1c7a5c00-93f3-4ae8-813a-a9f623335bc2

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
theorem _root_.solution {X Y : Scheme.{u}} (f : X ⟶ Y)
    (I : Y.IdealSheafData) (U : Y.Opens) (V : X.Opens) (h : V ≤ f ⁻¹ᵁ U) :
    restrictIdeal (I.comap f) V = (restrictIdeal I U).comap (f.resLE U V h) := by
  have hcomp : f.resLE U V h ≫ U.ι = V.ι ≫ f := by simp
  show (I.comap f).comap V.ι = (I.comap U.ι).comap (f.resLE U V h)
  rw [← Scheme.IdealSheafData.comap_comp, ← Scheme.IdealSheafData.comap_comp, hcomp]
end FunctorialResolution.EmbeddedResolution
