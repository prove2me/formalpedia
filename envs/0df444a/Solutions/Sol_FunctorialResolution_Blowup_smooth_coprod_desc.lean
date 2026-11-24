-- Prove2me | solution 1 for FunctorialResolution.Blowup.smooth_coprod_desc
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T11:46:32.219271+00:00
-- url     : https://prove2.me/submissions/ff26aeb4-4bc7-45b4-a5a1-6652e58714b7

import Mathlib
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_Blowup_BlowupBasic
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_Blowup_BlowupOpenCover
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_Schemes_SchemeCoproduct
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_Schemes_IdealSheafData
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_BlowupUniversalProperty
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_Blowup_BlowupCoproduct
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
universe u
open CategoryTheory AlgebraicGeometry CategoryTheory.Limits
namespace FunctorialResolution.Blowup
private theorem isZariskiLocalAtSource_smooth : IsZariskiLocalAtSource (@Smooth.{u}) :=
  @HasRingHomProperty.instIsZariskiLocalAtSource (@Smooth.{u}) RingHom.Smooth inferInstance
end FunctorialResolution.Blowup
end

set_option autoImplicit false
universe u
open CategoryTheory AlgebraicGeometry CategoryTheory.Limits
open FunctorialResolution FunctorialResolution.Blowup
namespace FunctorialResolution.Blowup
theorem _root_.solution {X A B : Scheme.{u}} (f : A ⟶ X) (g : B ⟶ X)
    (hf : Smooth f) (hg : Smooth g) : Smooth (coprod.desc f g) := by
  refine isZariskiLocalAtSource_smooth.of_openCover (coprodOpenCover.{u, u} A B) ?_
  intro i
  cases i with
  | inl _ =>
      show Smooth ((coprod.inl : A ⟶ A ⨿ B) ≫ coprod.desc f g)
      rw [coprod.inl_desc]
      exact hf
  | inr _ =>
      show Smooth ((coprod.inr : B ⟶ A ⨿ B) ≫ coprod.desc f g)
      rw [coprod.inr_desc]
      exact hg
end FunctorialResolution.Blowup
