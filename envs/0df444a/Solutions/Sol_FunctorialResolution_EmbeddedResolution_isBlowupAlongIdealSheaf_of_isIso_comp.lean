-- Prove2me | solution 1 for FunctorialResolution.EmbeddedResolution.isBlowupAlongIdealSheaf_of_isIso_comp
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T00:04:49.663056+00:00
-- url     : https://prove2.me/submissions/aa620027-e7b9-4c26-b8ae-530a9dddb4e0

import Mathlib
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_Blowup_BlowupBasic
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_Blowup_BlowupIsoOffCenter
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_Blowup_BlowupOpenCover
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_Blowup_BlowupProperties
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_IteratedBlowups_ClopenRestriction
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_Blowup_StrictTransform
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_Schemes_IdealSheafData
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_AlgebraicPreliminaries_OpenImmersionAppLE
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_AlgebraicPreliminaries_ReducedSubscheme
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_Schemes_SchemeMorphismProperties
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_BlowupUniversalProperty
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_ResolutionOfSingularities
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_IteratedBlowups_StrictTransform
import Theorems.Thm_FunctorialResolution_Blowup_IsLocallyGeneratedByNonZeroDivisor_comap_of_isOpenImmersion


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
namespace FunctorialResolution.EmbeddedResolution
theorem _root_.solution {X A B : Scheme.{u}} (f : A ⟶ X) (g : B ⟶ X) (e : A ⟶ B)
    [IsIso e] (hfac : e ≫ g = f) (I : X.IdealSheafData) (hg : Blowup.IsBlowupAlongIdealSheaf g I) :
    Blowup.IsBlowupAlongIdealSheaf f I := by
  obtain ⟨hcart, huniv⟩ := hg
  have h1 : I.comap f = (I.comap g).comap e := by
    rw [← Scheme.IdealSheafData.comap_comp, hfac]
  refine ⟨?_, ?_⟩
  · rw [h1]
    exact hcart.comap_of_isOpenImmersion e
  · intro Y q hq
    obtain ⟨t, ht, huniq⟩ := huniv Y q hq
    have ht' : t ≫ g = q := ht
    refine ⟨t ≫ inv e, ?_, ?_⟩
    · show (t ≫ inv e) ≫ f = q
      rw [← hfac, Category.assoc, IsIso.inv_hom_id_assoc]
      exact ht'
    · intro y hy
      have hy' : y ≫ f = q := hy
      have hye : y ≫ e = t := by
        refine huniq _ ?_
        show (y ≫ e) ≫ g = q
        rw [Category.assoc, hfac]
        exact hy'
      rw [← hye, Category.assoc, IsIso.hom_inv_id, Category.comp_id]
end FunctorialResolution.EmbeddedResolution
