-- Prove2me | solution 1 for FunctorialResolution.EmbeddedResolution.LocalResolutionData.smooth_lastStructMap_comp
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T17:24:08.107438+00:00
-- url     : https://prove2.me/submissions/8a9771e3-291e-4704-8e79-2dfb8a35c90a

import Mathlib
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_StrongResolution_LocalResolutionData
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_BlowupUniversalProperty
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_ResolutionOfSingularities
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_StrongResolution_LocalResolutionSmooth
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_LocalResolutionData_chartToLastObj_comp_lastStructMap_assoc
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
universe u
open CategoryTheory AlgebraicGeometry
noncomputable section
namespace FunctorialResolution.EmbeddedResolution
namespace LocalResolutionData
variable {k : Type u} [Field k] {X : Scheme.{u}} {f : X ⟶ Spec (CommRingCat.of k)}
  [LocallyOfFiniteType f] {s : SequenceOfBlowups X}
private theorem ringHom_smooth_appTop_of_smooth {A B : Scheme.{u}} [AlgebraicGeometry.IsAffine B]
    (g : A ⟶ B) (𝒲 : Scheme.OpenCover.{u, u} A)
    [∀ i, AlgebraicGeometry.IsAffine (𝒲.X i)]
    (hg : AlgebraicGeometry.Smooth g) (i : 𝒲.I₀) :
    RingHom.Smooth ((𝒲.f i ≫ g).appTop.hom) :=
  (AlgebraicGeometry.HasRingHomProperty.iff_of_source_openCover 𝒲).mp hg i
private theorem smooth_of_ringHom_smooth_appTop {A B : Scheme.{u}} [AlgebraicGeometry.IsAffine B]
    (g : A ⟶ B) (𝒲 : Scheme.OpenCover.{u, u} A)
    [∀ i, AlgebraicGeometry.IsAffine (𝒲.X i)]
    (h : ∀ i : 𝒲.I₀, RingHom.Smooth ((𝒲.f i ≫ g).appTop.hom)) :
    AlgebraicGeometry.Smooth g :=
  (AlgebraicGeometry.HasRingHomProperty.iff_of_source_openCover 𝒲).mpr h
private theorem smooth_chartToLastObj_comp (d : LocalResolutionData k f s) (j : d.cover.I₀) :
    AlgebraicGeometry.Smooth (d.chartToLastObj j ≫ (s.lastStructMap ≫ f)) := by
  rw [d.chartToLastObj_comp_lastStructMap_assoc j]
  exact (d.isResolution j).1
private theorem smooth_appTop_affineCover_chartToLastObj (d : LocalResolutionData k f s) (j : d.cover.I₀)
    (a : ((d.seq j).lastObj.affineCover).I₀) :
    RingHom.Smooth (((((d.seq j).lastObj.affineCover).f a ≫ d.chartToLastObj j)
      ≫ (s.lastStructMap ≫ f)).appTop.hom) := by
  have h := ringHom_smooth_appTop_of_smooth (d.chartToLastObj j ≫ (s.lastStructMap ≫ f))
    ((d.seq j).lastObj.affineCover) (smooth_chartToLastObj_comp d j) a
  rw [Category.assoc]
  exact h
end LocalResolutionData
end FunctorialResolution.EmbeddedResolution
end
end

set_option autoImplicit false
universe u
open CategoryTheory AlgebraicGeometry
noncomputable section
open FunctorialResolution FunctorialResolution.EmbeddedResolution
open FunctorialResolution.EmbeddedResolution.LocalResolutionData
variable {k : Type u} [Field k] {X : Scheme.{u}} {f : X ⟶ Spec (CommRingCat.of k)}
  [LocallyOfFiniteType f] {s : SequenceOfBlowups X}
namespace FunctorialResolution.EmbeddedResolution.LocalResolutionData
theorem _root_.solution (d : LocalResolutionData k f s) :
    AlgebraicGeometry.Smooth (s.lastStructMap ≫ f) := by
  have haffine : ∀ i : (d.lastObjCover.bind fun j => (d.lastObjCover.X j).affineCover).I₀,
      AlgebraicGeometry.IsAffine
        ((d.lastObjCover.bind fun j => (d.lastObjCover.X j).affineCover).X i) := by
    rintro ⟨j, a⟩
    exact inferInstanceAs (AlgebraicGeometry.IsAffine (((d.lastObjCover.X j).affineCover).X a))
  refine smooth_of_ringHom_smooth_appTop (s.lastStructMap ≫ f)
    (d.lastObjCover.bind fun j => (d.lastObjCover.X j).affineCover) ?_
  rintro ⟨j, a⟩
  exact smooth_appTop_affineCover_chartToLastObj d j a
end FunctorialResolution.EmbeddedResolution.LocalResolutionData
