-- Prove2me | solution 1 for FunctorialResolution.EmbeddedResolution.isPullback_initial_of_isEmpty
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T11:49:05.969747+00:00
-- url     : https://prove2.me/submissions/5dbe9ca3-990a-46d3-a520-eb40d8a4861b

import Mathlib
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_AlgebraicPreliminaries_CoproductBaseChange
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_AlgebraicPreliminaries_BinaryCoproductBaseChange

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
universe u
open FunctorialResolution FunctorialResolution.EmbeddedResolution
namespace FunctorialResolution.EmbeddedResolution
theorem _root_.solution {X Y Y' : Scheme.{u}} (f : X ⟶ Y) (u : Y' ⟶ Y)
    (h : ∀ (P : Scheme.{u}) (a : P ⟶ X) (b : P ⟶ Y'), a ≫ f = b ≫ u → IsEmpty P) :
    IsPullback (initial.to X) (initial.to Y') f u := by
  have hw : CommSq (initial.to X) (initial.to Y') f u := ⟨initial.hom_ext _ _⟩
  refine IsPullback.of_isLimit' hw (PullbackCone.isLimitAux' _ (fun s => ?_))
  have hinit : IsInitial s.pt := isInitialOfIsEmptyScheme (h s.pt s.fst s.snd s.condition)
  refine ⟨hinit.to _, hinit.hom_ext _ _, hinit.hom_ext _ _, ?_⟩
  intro m _ _
  exact hinit.hom_ext _ _
end FunctorialResolution.EmbeddedResolution
