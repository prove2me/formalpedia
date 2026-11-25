-- Prove2me | solution 1 for FunctorialResolution.EmbeddedResolution.EmbeddedBlowupSequence.support_centerOffDetached_subset_preimage
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T17:31:13.775369+00:00
-- url     : https://prove2.me/submissions/6f4a13c4-55ec-49e2-9e47-cd6a48dc2b2b

import Mathlib
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_Blowup_BlowupBasic
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_Blowup_BlowupCoproduct
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_IteratedBlowups_BlowupSequenceBasic
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_IdealPrincipalization_MarkedBlowupSequence_IdealBlowupSequence
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_StrongResolution_EmbeddedBlowupSequence
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_StrongResolution_EmbeddedStrictTransform
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_BlowupUniversalProperty
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_ResolutionOfSingularities
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_StrongResolution_StrictTransformTower
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_EmbeddedBlowupSequence_comapAmbientCenter_le_centerOffDetached
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace Opposite
noncomputable section
namespace FunctorialResolution.EmbeddedResolution
namespace EmbeddedBlowupSequence
variable {k : Type u} [Field k] [CharZero k] {Y : Scheme.{u}} [AlgebraicGeometry.IsAffine Y]
  {pY : Y ⟶ Spec (CommRingCat.of k)} [AlgebraicGeometry.LocallyOfFiniteType pY]
variable (S : EmbeddedBlowupSequence k Y pY)
private theorem hom_comp_base_apply {A B C : Scheme.{u}} (f : A ⟶ B) (g : B ⟶ C)
    (x : ↥A) : ⇑(f ≫ g).base x = ⇑g.base (⇑f.base x) := rfl
end EmbeddedBlowupSequence
variable {k : Type u} [Field k] [CharZero k] {Y : Scheme.{u}} [AlgebraicGeometry.IsAffine Y]
  {pY : Y ⟶ Spec (CommRingCat.of k)} [AlgebraicGeometry.LocallyOfFiniteType pY]
end FunctorialResolution.EmbeddedResolution
end
end

set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace Opposite
noncomputable section
open FunctorialResolution FunctorialResolution.EmbeddedResolution
open FunctorialResolution.EmbeddedResolution.EmbeddedBlowupSequence
variable {k : Type u} [Field k] [CharZero k] {Y : Scheme.{u}} [AlgebraicGeometry.IsAffine Y]
  {pY : Y ⟶ Spec (CommRingCat.of k)} [AlgebraicGeometry.LocallyOfFiniteType pY]
variable (S : EmbeddedBlowupSequence k Y pY)
namespace FunctorialResolution.EmbeddedResolution.EmbeddedBlowupSequence
theorem _root_.solution (i : ℕ) :
    ((S.centerOffDetached i).support : Set ↥(S.strictTransform i)) ⊆
      ⇑(S.strictTransformι i).base ⁻¹' ((S.ambientCenter i).support : Set ↥(S.schemeAt i)) := by
  have h1 : (S.ambientCenter i).comap (S.strictTransformι i) ≤ S.centerOffDetached i :=
    S.comapAmbientCenter_le_centerOffDetached i
  have h2 : S.ambientCenter i ≤ (S.centerOffDetached i).map (S.strictTransformι i) :=
    Scheme.IdealSheafData.le_map_iff_comap_le.mpr h1
  have hu : (S.centerOffDetached i).subschemeMap (S.ambientCenter i) (S.strictTransformι i) h2 ≫
        (S.ambientCenter i).subschemeι =
      (S.centerOffDetached i).subschemeι ≫ S.strictTransformι i :=
    Scheme.IdealSheafData.subschemeMap_subschemeι ..
  intro x hx
  rw [← Scheme.IdealSheafData.range_subschemeι] at hx
  obtain ⟨z, rfl⟩ := hx
  have key : ⇑((S.centerOffDetached i).subschemeMap (S.ambientCenter i) (S.strictTransformι i) h2 ≫
        (S.ambientCenter i).subschemeι).base z =
      ⇑((S.centerOffDetached i).subschemeι ≫ S.strictTransformι i).base z := by
    rw [hu]
  rw [hom_comp_base_apply, hom_comp_base_apply] at key
  rw [← Scheme.IdealSheafData.range_subschemeι]
  exact ⟨_, key⟩
end FunctorialResolution.EmbeddedResolution.EmbeddedBlowupSequence
