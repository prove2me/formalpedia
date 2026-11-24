-- Prove2me | solution 1 for FunctorialResolution.Blowup.ker_comp_coprod_inl_comap_inr
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T11:46:29.357416+00:00
-- url     : https://prove2.me/submissions/5f6c6f4b-b79e-464c-8909-3c7b05a8723a

import Mathlib
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_Blowup_BlowupBasic
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_Blowup_BlowupOpenCover
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_Schemes_SchemeCoproduct
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_Schemes_IdealSheafData
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_BlowupUniversalProperty
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_Blowup_BlowupCoproduct
import Theorems.Thm_FunctorialResolution_Blowup_comap_eq_top_of_notMem_support
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
private theorem range_comp_coprod_inl_subset {X Y Z : Scheme.{u}} (f : Z ⟶ X) :
    Set.range ⇑(f ≫ (coprod.inl : X ⟶ X ⨿ Y)).base
      ⊆ Set.range ⇑(coprod.inl : X ⟶ X ⨿ Y).base := by
  rintro _ ⟨z, rfl⟩
  exact ⟨f.base z, by simp⟩
end FunctorialResolution.Blowup
end

set_option autoImplicit false
universe u
open CategoryTheory AlgebraicGeometry CategoryTheory.Limits
open FunctorialResolution FunctorialResolution.Blowup
namespace FunctorialResolution.Blowup
theorem _root_.solution {X Y Z : Scheme.{u}} (f : Z ⟶ X)
    [QuasiCompact (f ≫ (coprod.inl : X ⟶ X ⨿ Y))] :
    (f ≫ (coprod.inl : X ⟶ X ⨿ Y)).ker.comap (coprod.inr : Y ⟶ X ⨿ Y) = ⊤ := by
  refine comap_eq_top_of_notMem_support (coprod.inr : Y ⟶ X ⨿ Y)
    ((f ≫ (coprod.inl : X ⟶ X ⨿ Y)).ker) ?_
  intro y hy
  have hy' : (coprod.inr : Y ⟶ X ⨿ Y).base y ∈
      ((f ≫ (coprod.inl : X ⟶ X ⨿ Y)).ker.support : Set ↥(X ⨿ Y)) := hy
  rw [Scheme.Hom.support_ker] at hy'
  have hsub : closure (Set.range ⇑(f ≫ (coprod.inl : X ⟶ X ⨿ Y)).base)
      ⊆ Set.range ⇑(coprod.inl : X ⟶ X ⨿ Y).base :=
    closure_minimal (range_comp_coprod_inl_subset f) (isClosed_range_coprod_inl X Y)
  have h2 : (coprod.inr : Y ⟶ X ⨿ Y).base y ∈ Set.range ⇑(coprod.inr : Y ⟶ X ⨿ Y).base :=
    Set.mem_range_self y
  rw [range_coprod_inr_eq_compl X Y] at h2
  exact h2 (hsub hy')
end FunctorialResolution.Blowup
