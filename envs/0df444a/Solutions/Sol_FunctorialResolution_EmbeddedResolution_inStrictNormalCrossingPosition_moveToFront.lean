-- Prove2me | solution 1 for FunctorialResolution.EmbeddedResolution.inStrictNormalCrossingPosition_moveToFront
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T17:21:33.928341+00:00
-- url     : https://prove2.me/submissions/4f039d51-d0ad-4aff-bd53-f148c442dbf1

import Mathlib
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_EtaleCoordinates_StrictNormalCrossings
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_IdealPrincipalization_DivisorReduction_StrictNormalCrossingsMoveToFront
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_indexBeforeMoveToFront_injective
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_getElem_moveToFront
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_mem_of_mem_moveToFront
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
    (p : X ⟶ Spec (CommRingCat.of k)) (E : List X.IdealSheafData) (j : ℕ)
    (hj : j < E.length) (hE : InStrictNormalCrossingPosition p E) :
    InStrictNormalCrossingPosition p (moveToFront E j) := by
  refine ⟨?_, ?_⟩
  · intro D hD
    exact hE.1 D (mem_of_mem_moveToFront E j hj D hD)
  · intro x
    obtain ⟨U, hxU, m, c, a, h1, h2, h3⟩ := hE.2 x
    have hlen : (moveToFront E j).length = E.length := length_moveToFront E j hj
    have hlt : ∀ i, i < (moveToFront E j).length → indexBeforeMoveToFront j i < E.length := by
      intro i hi
      refine indexBeforeMoveToFront_lt_length E j hj i ?_
      rw [hlen] at hi
      exact hi
    have hEq : ∀ i, ∀ h : i < (moveToFront E j).length,
        ((moveToFront E j)[i]'h) = E[indexBeforeMoveToFront j i]'(hlt i h) :=
      fun i h => getElem_moveToFront E j hj i h
    obtain ⟨k1, k2, k3⟩ := chartAssignment_comp_of_injective c a E (moveToFront E j) (indexBeforeMoveToFront j)
      (indexBeforeMoveToFront_injective j) hlt hEq h1 h2 h3
    exact ⟨U, hxU, m, c, a ∘ indexBeforeMoveToFront j, k1, k2, k3⟩
end FunctorialResolution.EmbeddedResolution
