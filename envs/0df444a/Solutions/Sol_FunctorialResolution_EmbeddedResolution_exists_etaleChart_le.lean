-- Prove2me | solution 1 for FunctorialResolution.EmbeddedResolution.exists_etaleChart_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T17:29:14.390872+00:00
-- url     : https://prove2.me/submissions/883b68f1-5d48-4b03-b943-daad3d2d1a0f

import Mathlib
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_EtaleCoordinates_StrictNormalCrossings
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_Schemes_AffineOpens
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_BlowupUniversalProperty
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_ResolutionOfSingularities
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_EtaleCoordinates_EtaleChartExistence
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_exists_etaleChart
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_HasStrictNormalCrossingsWith_exists_etaleChart
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_InStrictNormalCrossingPositionAt_exists_etaleChart


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
theorem _root_.solution {X : Scheme.{u}} {k : Type u} [Field k]
    (p : X ⟶ Spec (CommRingCat.of k)) [AlgebraicGeometry.Smooth p] (x : X)
    (W : X.Opens) (hx : x ∈ W) :
    ∃ (U : X.Opens) (m : ℕ), x ∈ U ∧ U ≤ W ∧ IsAffineOpen U ∧ Nonempty (EtaleChart p U m) := by
  obtain ⟨U, m, hxU, hU, ⟨c⟩⟩ := exists_etaleChart p x
  have hxUW : x ∈ (U ⊓ W : X.Opens) := ⟨hxU, hx⟩
  obtain ⟨f, hfle, hxf⟩ := hU.exists_basicOpen_le (⟨x, hxUW⟩ : (U ⊓ W : X.Opens)) hxU
  have hle : X.basicOpen f ≤ U := X.basicOpen_le f
  exact ⟨X.basicOpen f, m, hxf, le_trans hfle inf_le_right, hU.basicOpen f, ⟨c.restrict hle⟩⟩
end FunctorialResolution.EmbeddedResolution
