-- Prove2me | solution 1 for FunctorialResolution.EmbeddedResolution.NonzeroOnComponents.comap_of_generalizingMap
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T12:05:28.595493+00:00
-- url     : https://prove2.me/submissions/4550a8d4-9934-4649-b551-640757fed09b

import Mathlib
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_EtaleCoordinates_StrictNormalCrossings
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_ResolutionDescent_SupportFlatPullback
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_closure_image_mem_irreducibleComponents_of_generalizingMap
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_support_comap

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
universe u
open CategoryTheory AlgebraicGeometry TopologicalSpace
noncomputable section
open FunctorialResolution FunctorialResolution.EmbeddedResolution
open FunctorialResolution.EmbeddedResolution.NonzeroOnComponents
namespace FunctorialResolution.EmbeddedResolution.NonzeroOnComponents
theorem _root_.solution {X Y : Scheme.{u}} {I : Y.IdealSheafData}
    (hI : NonzeroOnComponents I) (f : X ⟶ Y)
    (hf : GeneralizingMap (fun x : ↥X => f x)) :
    NonzeroOnComponents (I.comap f) := by
  intro T hT hsub
  have hsub' : closure ((fun x : ↥X => f x) '' T) ⊆ (I.support : Set ↥Y) := by
    refine closure_minimal ?_ I.support.2
    rintro _ ⟨x, hxT, rfl⟩
    have hx : x ∈ ((I.comap f).support : Set ↥X) := hsub hxT
    rw [support_comap f I] at hx
    exact hx
  exact hI _ (closure_image_mem_irreducibleComponents_of_generalizingMap f hf hT) hsub'
end FunctorialResolution.EmbeddedResolution.NonzeroOnComponents
