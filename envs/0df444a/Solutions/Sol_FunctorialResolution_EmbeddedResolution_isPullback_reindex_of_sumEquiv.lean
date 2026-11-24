-- Prove2me | solution 1 for FunctorialResolution.EmbeddedResolution.isPullback_reindex_of_sumEquiv
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T23:18:53.062644+00:00
-- url     : https://prove2.me/submissions/c5e7560a-f498-43f4-8f18-45e5257e8874

import Mathlib
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_Blowup_BlowupBasic
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_IteratedBlowups_BlowupSequenceRelations
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_EtaleCoordinates_AffineSpaceCoordinates
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_ResolutionDescent_AffineResolutionRule
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_BlowupUniversalProperty
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_ResolutionOfSingularities
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_ResolutionDescent_AffineSpaceProduct
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_homOfSumCoords_appTop_coord_inl
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_homOfSumCoords_appTop_coord_inr
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_coordVectorInl_inl
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_coordVectorInl_inr
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_coordVectorInr_inl
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_coordVectorInr_inr
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_pullbackCoord_def
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] FunctorialResolution.EmbeddedResolution.coordVectorInl_inl
attribute [local simp] FunctorialResolution.EmbeddedResolution.coordVectorInl_inr
attribute [local simp] FunctorialResolution.EmbeddedResolution.coordVectorInr_inl
attribute [local simp] FunctorialResolution.EmbeddedResolution.coordVectorInr_inr
attribute [local simp] FunctorialResolution.EmbeddedResolution.pullbackCoord_def


attribute [local simp] FunctorialResolution.EmbeddedResolution.homOfSumCoords_appTop_coord_inl
attribute [local simp] FunctorialResolution.EmbeddedResolution.homOfSumCoords_appTop_coord_inr
section
universe u
open CategoryTheory AlgebraicGeometry TopologicalSpace
noncomputable section
namespace FunctorialResolution.EmbeddedResolution
private theorem homOfSumCoords_comp_reindex_inl {n₁ n₂ n : Type u} (e : n₁ ⊕ n₂ ≃ n) (S : Scheme.{u})
    {X : Scheme.{u}} (f : X ⟶ AffineSpace n₁ S) (g : X ⟶ AffineSpace n₂ S) :
    homOfSumCoords e S f g ≫ AffineSpace.reindex (S := S) (fun a : n₁ => e (Sum.inl a)) = f := by
  refine AffineSpace.hom_ext ?_ (fun a => ?_)
  · simp [homOfSumCoords]
  · rw [AlgebraicGeometry.Scheme.Hom.comp_appTop, CommRingCat.comp_apply]
    simp
private theorem homOfSumCoords_comp_reindex_inr {n₁ n₂ n : Type u} (e : n₁ ⊕ n₂ ≃ n) (S : Scheme.{u})
    {X : Scheme.{u}} (f : X ⟶ AffineSpace n₁ S) (g : X ⟶ AffineSpace n₂ S)
    (hfg : f ≫ (AffineSpace n₁ S ↘ S) = g ≫ (AffineSpace n₂ S ↘ S)) :
    homOfSumCoords e S f g ≫ AffineSpace.reindex (S := S) (fun b : n₂ => e (Sum.inr b)) = g := by
  refine AffineSpace.hom_ext ?_ (fun b => ?_)
  · simpa [homOfSumCoords] using hfg
  · rw [AlgebraicGeometry.Scheme.Hom.comp_appTop, CommRingCat.comp_apply]
    simp
private theorem eq_homOfSumCoords_of_comp_reindex {n₁ n₂ n : Type u} (e : n₁ ⊕ n₂ ≃ n) (S : Scheme.{u})
    {X : Scheme.{u}} (f : X ⟶ AffineSpace n₁ S) (g : X ⟶ AffineSpace n₂ S)
    (m : X ⟶ AffineSpace n S)
    (h₁ : m ≫ AffineSpace.reindex (S := S) (fun a : n₁ => e (Sum.inl a)) = f)
    (h₂ : m ≫ AffineSpace.reindex (S := S) (fun b : n₂ => e (Sum.inr b)) = g) :
    m = homOfSumCoords e S f g := by
  refine AffineSpace.hom_ext ?_ (fun i => ?_)
  · have h : (m ≫ AffineSpace.reindex (S := S) (fun a : n₁ => e (Sum.inl a))) ≫
        (AffineSpace n₁ S ↘ S) = f ≫ (AffineSpace n₁ S ↘ S) := by rw [h₁]
    simpa [homOfSumCoords] using h
  · obtain ⟨j, rfl⟩ : ∃ j, e j = i := ⟨e.symm i, e.apply_symm_apply i⟩
    obtain (a | b) := j
    · have h : (m ≫ AffineSpace.reindex (S := S) (fun a : n₁ => e (Sum.inl a))).appTop
          (AffineSpace.coord S a) = f.appTop (AffineSpace.coord S a) := by rw [h₁]
      rw [AlgebraicGeometry.Scheme.Hom.comp_appTop, CommRingCat.comp_apply] at h
      simpa using h
    · have h : (m ≫ AffineSpace.reindex (S := S) (fun b : n₂ => e (Sum.inr b))).appTop
          (AffineSpace.coord S b) = g.appTop (AffineSpace.coord S b) := by rw [h₂]
      rw [AlgebraicGeometry.Scheme.Hom.comp_appTop, CommRingCat.comp_apply] at h
      simpa using h
end FunctorialResolution.EmbeddedResolution
end
end

set_option autoImplicit false
universe u
open CategoryTheory AlgebraicGeometry TopologicalSpace
noncomputable section
open FunctorialResolution FunctorialResolution.EmbeddedResolution
namespace FunctorialResolution.EmbeddedResolution
theorem _root_.solution {n₁ n₂ n : Type u} (e : n₁ ⊕ n₂ ≃ n) (S : Scheme.{u}) :
    IsPullback
      (AffineSpace.reindex (S := S) (fun a : n₁ => e (Sum.inl a)))
      (AffineSpace.reindex (S := S) (fun b : n₂ => e (Sum.inr b)))
      (AffineSpace n₁ S ↘ S) (AffineSpace n₂ S ↘ S) := by
  have hcomm : CommSq
      (AffineSpace.reindex (S := S) (fun a : n₁ => e (Sum.inl a)))
      (AffineSpace.reindex (S := S) (fun b : n₂ => e (Sum.inr b)))
      (AffineSpace n₁ S ↘ S) (AffineSpace n₂ S ↘ S) := ⟨by simp⟩
  have hcond : Limits.pullback.fst (AffineSpace n₁ S ↘ S) (AffineSpace n₂ S ↘ S) ≫
      (AffineSpace n₁ S ↘ S) =
      Limits.pullback.snd (AffineSpace n₁ S ↘ S) (AffineSpace n₂ S ↘ S) ≫
      (AffineSpace n₂ S ↘ S) := Limits.pullback.condition
  have hA : homOfSumCoords e S
      (Limits.pullback.fst (AffineSpace n₁ S ↘ S) (AffineSpace n₂ S ↘ S))
      (Limits.pullback.snd (AffineSpace n₁ S ↘ S) (AffineSpace n₂ S ↘ S)) ≫
      AffineSpace.reindex (S := S) (fun a : n₁ => e (Sum.inl a)) =
      Limits.pullback.fst (AffineSpace n₁ S ↘ S) (AffineSpace n₂ S ↘ S) :=
    homOfSumCoords_comp_reindex_inl e S _ _
  have hB : homOfSumCoords e S
      (Limits.pullback.fst (AffineSpace n₁ S ↘ S) (AffineSpace n₂ S ↘ S))
      (Limits.pullback.snd (AffineSpace n₁ S ↘ S) (AffineSpace n₂ S ↘ S)) ≫
      AffineSpace.reindex (S := S) (fun b : n₂ => e (Sum.inr b)) =
      Limits.pullback.snd (AffineSpace n₁ S ↘ S) (AffineSpace n₂ S ↘ S) :=
    homOfSumCoords_comp_reindex_inr e S _ _ hcond
  have hid : (𝟙 (AffineSpace n S)) = homOfSumCoords e S
      (AffineSpace.reindex (S := S) (fun a : n₁ => e (Sum.inl a)))
      (AffineSpace.reindex (S := S) (fun b : n₂ => e (Sum.inr b))) :=
    eq_homOfSumCoords_of_comp_reindex e S _ _ _ (Category.id_comp _) (Category.id_comp _)
  refine IsPullback.of_iso_pullback hcomm
    { hom := Limits.pullback.lift _ _ hcomm.w
      inv := homOfSumCoords e S
        (Limits.pullback.fst (AffineSpace n₁ S ↘ S) (AffineSpace n₂ S ↘ S))
        (Limits.pullback.snd (AffineSpace n₁ S ↘ S) (AffineSpace n₂ S ↘ S))
      hom_inv_id := ?_
      inv_hom_id := ?_ }
    (Limits.pullback.lift_fst _ _ _) (Limits.pullback.lift_snd _ _ _)
  · rw [hid]
    refine eq_homOfSumCoords_of_comp_reindex e S _ _ _ ?_ ?_
    · rw [Category.assoc, hA]
      exact Limits.pullback.lift_fst _ _ _
    · rw [Category.assoc, hB]
      exact Limits.pullback.lift_snd _ _ _
  · refine Limits.pullback.hom_ext ?_ ?_
    · rw [Category.assoc, Limits.pullback.lift_fst, Category.id_comp]
      exact hA
    · rw [Category.assoc, Limits.pullback.lift_snd, Category.id_comp]
      exact hB
end FunctorialResolution.EmbeddedResolution
