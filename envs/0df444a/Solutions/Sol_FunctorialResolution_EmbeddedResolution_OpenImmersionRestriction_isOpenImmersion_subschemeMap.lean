-- Prove2me | solution 1 for FunctorialResolution.EmbeddedResolution.OpenImmersionRestriction.isOpenImmersion_subschemeMap
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T17:21:50.936809+00:00
-- url     : https://prove2.me/submissions/3aa72620-7b17-46a7-ac61-c6e82f35ee58

import Mathlib
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_Blowup_BlowupOpenCover
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_EtaleCoordinates_StrictNormalCrossings
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_ResolutionDescent_SupportFlatPullback
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_BlowupUniversalProperty
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_ResolutionOfSingularities
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_EtaleCoordinates_OpenRestriction
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
universe u
open CategoryTheory AlgebraicGeometry TopologicalSpace
noncomputable section
namespace FunctorialResolution.EmbeddedResolution
namespace OpenImmersionRestriction
private theorem exists_subschemeMap_isOpenImmersion {V W : Scheme.{u}} (f : V ⟶ W)
    [IsOpenImmersion f] (D : W.IdealSheafData) :
    ∃ g : (D.comap f).subscheme ⟶ D.subscheme,
      IsOpenImmersion g ∧ g ≫ D.subschemeι = (D.comap f).subschemeι ≫ f := by
  have h₁ : IsOpenImmersion (Limits.pullback.snd f D.subschemeι) := inferInstance
  have h₂ : IsOpenImmersion (D.comapIso f).hom := inferInstance
  refine ⟨(D.comapIso f).hom ≫ Limits.pullback.snd f D.subschemeι, inferInstance, ?_⟩
  rw [Category.assoc, ← Limits.pullback.condition, ← Category.assoc,
    Scheme.IdealSheafData.comapIso_hom_fst]
end OpenImmersionRestriction
end FunctorialResolution.EmbeddedResolution
end
end

set_option autoImplicit false
universe u
open CategoryTheory AlgebraicGeometry TopologicalSpace
noncomputable section
open FunctorialResolution FunctorialResolution.EmbeddedResolution
open FunctorialResolution.EmbeddedResolution.OpenImmersionRestriction
namespace FunctorialResolution.EmbeddedResolution.OpenImmersionRestriction
theorem _root_.solution {V W : Scheme.{u}} (f : V ⟶ W) [IsOpenImmersion f]
    (D : W.IdealSheafData) (g : (D.comap f).subscheme ⟶ D.subscheme)
    (hg : g ≫ D.subschemeι = (D.comap f).subschemeι ≫ f) :
    IsOpenImmersion g := by
  obtain ⟨g', hg', hg'fac⟩ := exists_subschemeMap_isOpenImmersion f D
  have : Mono D.subschemeι := inferInstance
  have heq : g = g' := by
    refine (cancel_mono D.subschemeι).mp ?_
    rw [hg, hg'fac]
  rw [heq]
  exact hg'
end FunctorialResolution.EmbeddedResolution.OpenImmersionRestriction
