-- Prove2me | solution 1 for FunctorialResolution.EmbeddedResolution.smooth_of_iSup_eq_top
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T17:00:38.140431+00:00
-- url     : https://prove2.me/submissions/3438cb5a-50dc-4abc-a2c9-4fe703b02eaa

import Mathlib
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_Blowup_BlowupProperties
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_IteratedBlowups_ClopenRestriction
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_EtaleCoordinates_ChartRing
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_EtaleCoordinates_CoordinateSubscheme
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_EtaleCoordinates_EtaleChartExistence
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_EtaleCoordinates_StrictNormalCrossings
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_Schemes_IdealSheafData
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_StrongResolution_AffineSpaceSmooth
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_BlowupUniversalProperty
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_ResolutionOfSingularities
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_EtaleCoordinates_CoordinateDivisorSmoothness

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
universe u
open CategoryTheory Opposite AlgebraicGeometry TopologicalSpace
open FunctorialResolution FunctorialResolution.EmbeddedResolution
variable {X : Scheme.{u}} {k : Type u} [Field k] {p : X ⟶ Spec (CommRingCat.of k)} {m : ℕ}
namespace FunctorialResolution.EmbeddedResolution
theorem _root_.solution {W Y : Scheme.{u}} (f : W ⟶ Y) {ι : Sort*} (U : ι → W.Opens)
    (hU : iSup U = ⊤) (h : ∀ i, Smooth ((U i).ι ≫ f)) : Smooth f := by
  have i3 : HasRingHomProperty (@Smooth.{u})
      (fun {R S : Type u} [CommRing R] [CommRing S] (g : R →+* S) => g.Smooth) := inferInstance
  have hloc : IsZariskiLocalAtSource (@Smooth.{u}) :=
    @HasRingHomProperty.instIsZariskiLocalAtSource _ _ i3
  have hVtop : (⨆ i : PLift ι, U i.down) = ⊤ := by
    rw [← hU]
    exact le_antisymm (iSup_le fun i => le_iSup U i.down)
      (iSup_le fun i => le_iSup (fun j : PLift ι => U j.down) (PLift.up i))
  exact (IsZariskiLocalAtSource.iff_of_iSup_eq_top (fun i : PLift ι => U i.down) hVtop).mpr
    fun i => h i.down
end FunctorialResolution.EmbeddedResolution
