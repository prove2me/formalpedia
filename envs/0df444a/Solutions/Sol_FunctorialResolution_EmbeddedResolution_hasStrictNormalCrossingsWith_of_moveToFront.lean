-- Prove2me | solution 1 for FunctorialResolution.EmbeddedResolution.hasStrictNormalCrossingsWith_of_moveToFront
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T17:21:26.942265+00:00
-- url     : https://prove2.me/submissions/cd2b5df1-d7ca-4aca-a2b9-077e52f1c5a7

import Mathlib
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_EtaleCoordinates_StrictNormalCrossings
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_IdealPrincipalization_DivisorReduction_StrictNormalCrossingsMoveToFront
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_indexInMoveToFront_injective
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_getElem_eq_getElem_moveToFront
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_chartAssignment_comp_of_injective

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
variable {α : Type*}
namespace FunctorialResolution.EmbeddedResolution
theorem _root_.solution {X : Scheme.{u}} {k : Type u} [Field k]
    (p : X ⟶ Spec (CommRingCat.of k)) (Z : X.IdealSheafData)
    (E : List X.IdealSheafData) (j : ℕ) (hj : j < E.length)
    (hZ : HasStrictNormalCrossingsWith p Z (moveToFront E j)) :
    HasStrictNormalCrossingsWith p Z E := by
  intro x hx
  obtain ⟨U, hxU, m, c, a, S, h1, h2, h3, h4⟩ := hZ x hx
  have hlt : ∀ i, i < E.length → indexInMoveToFront j i < (moveToFront E j).length :=
    fun i hi => indexInMoveToFront_lt_length E j hj i hi
  have hEq : ∀ i, ∀ h : i < E.length,
      (E[i]'h) = (moveToFront E j)[indexInMoveToFront j i]'(hlt i h) :=
    fun i h => getElem_eq_getElem_moveToFront E j hj i h
  obtain ⟨k1, k2, k3⟩ := chartAssignment_comp_of_injective c a (moveToFront E j) E (indexInMoveToFront j)
    (indexInMoveToFront_injective j) hlt hEq h1 h2 h3
  exact ⟨U, hxU, m, c, a ∘ indexInMoveToFront j, S, k1, k2, k3, h4⟩
end FunctorialResolution.EmbeddedResolution
