-- Prove2me | solution 1 for FunctorialResolution.EmbeddedResolution.isReduced_baseChange_sigmaOpensDesc
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T11:49:08.394808+00:00
-- url     : https://prove2.me/submissions/399af5a7-2cac-44cd-b69b-bac8ad782b2e

import Mathlib
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_AlgebraicPreliminaries_DisjointUnionOfOpens
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_BlowupUniversalProperty
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_ResolutionOfSingularities
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_ResolutionDescent_FieldExtensionEtaleCover
import Theorems.Thm_P2M_FunctorialResolution_EmbeddedResolution_sigma___sigmaOpensDesc_a310daec50eb

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace FunctorialResolution.EmbeddedResolution
noncomputable section
variable {k : Type u} [Field k] {X W : Scheme.{u}}
private theorem isReduced_of_isReduced_stalk (Y : Scheme.{u})
    (h : ∀ y : ↥Y, _root_.IsReduced (Y.presheaf.stalk y)) : IsReduced Y := by
  have : ∀ y : ↥Y, _root_.IsReduced (Y.presheaf.stalk y) := h
  exact AlgebraicGeometry.isReduced_of_isReduced_stalk Y
private theorem isReduced_stalk_of_isOpenImmersion {A B : Scheme.{u}} (w : A ⟶ B)
    [IsOpenImmersion w] [IsReduced B] (a : ↥A) : _root_.IsReduced (A.presheaf.stalk a) :=
  isReduced_of_injective (CategoryTheory.inv (w.stalkMap a)).hom
    (ConcreteCategory.bijective_of_isIso (CategoryTheory.inv (w.stalkMap a))).1
private theorem isReduced_of_isReduced_stalk_of_cover {Y : Scheme.{u}} {ι : Type u} {Z : ι → Scheme.{u}}
    (j : ∀ i, Z i ⟶ Y) (hj : ∀ i, IsOpenImmersion (j i))
    (hZ : ∀ (i : ι) (z : ↥(Z i)), _root_.IsReduced ((Z i).presheaf.stalk z))
    (hcov : ∀ y : ↥Y, ∃ (i : ι) (z : ↥(Z i)), (j i).base z = y) : IsReduced Y := by
  refine isReduced_of_isReduced_stalk Y ?_
  intro y
  obtain ⟨i, z, rfl⟩ := hcov y
  have := hj i
  have := hZ i z
  exact isReduced_of_injective ((j i).stalkMap z).hom
    (ConcreteCategory.bijective_of_isIso ((j i).stalkMap z)).1
private theorem sigma_jointly_surjective {ι : Type u} (Z : ι → Scheme.{u}) (x : ↥(∐ Z)) :
    ∃ (i : ι) (y : ↥(Z i)), (Sigma.ι Z i).base y = x := by
  obtain ⟨y, hy⟩ := (sigmaOpenCover Z).covers x
  exact ⟨_, y, hy⟩
private theorem exists_pullback_snd_base_eq {A B C' : Scheme.{u}} (g1 : A ⟶ C') (g2 : B ⟶ C')
    (a : ↥A) (b : ↥B) (h : g1.base a = g2.base b) :
    ∃ z : ↥(pullback g1 g2), (pullback.snd g1 g2).base z = b := by
  obtain ⟨z, _, hz2⟩ := Scheme.Pullback.exists_preimage_pullback (f := g1) (g := g2) a b h
  exact ⟨z, hz2⟩
end
end FunctorialResolution.EmbeddedResolution
end

set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open FunctorialResolution FunctorialResolution.EmbeddedResolution
noncomputable section
variable {k : Type u} [Field k] {X W : Scheme.{u}}
namespace FunctorialResolution.EmbeddedResolution
theorem _root_.solution (f : X ⟶ Spec (CommRingCat.of k))
    (K : Type u) [Field K] [Algebra k K] [IsReduced (baseChange f K)]
    {ι : Type u} (U : ι → X.Opens) :
    IsReduced (baseChange (sigmaOpensDesc X U ≫ f) K) := by
  have hsq : ∀ i : ι, IsPullback
      (pullback.snd (Sigma.ι (fun i => (U i).toScheme) i)
          (baseChangeProjection (sigmaOpensDesc X U ≫ f) K) ≫
        baseChangeMap f (sigmaOpensDesc X U) K)
      (pullback.fst (Sigma.ι (fun i => (U i).toScheme) i)
        (baseChangeProjection (sigmaOpensDesc X U ≫ f) K))
      (baseChangeProjection f K) ((U i).ι) := by
    intro i
    have h := IsPullback.paste_horiz
      (IsPullback.of_hasPullback (Sigma.ι (fun i => (U i).toScheme) i)
        (baseChangeProjection (sigmaOpensDesc X U ≫ f) K)).flip
      (isPullback_baseChangeMap f (sigmaOpensDesc X U) K)
    rwa [sigma_ι_sigmaOpensDesc X U i] at h
  refine isReduced_of_isReduced_stalk_of_cover
    (Z := fun i => pullback (Sigma.ι (fun i => (U i).toScheme) i)
      (baseChangeProjection (sigmaOpensDesc X U ≫ f) K))
    (fun i => pullback.snd (Sigma.ι (fun i => (U i).toScheme) i)
      (baseChangeProjection (sigmaOpensDesc X U ≫ f) K))
    (fun i => inferInstance) (fun i z => ?_) ?_
  · have : IsOpenImmersion (pullback.snd (Sigma.ι (fun i => (U i).toScheme) i)
        (baseChangeProjection (sigmaOpensDesc X U ≫ f) K) ≫
        baseChangeMap f (sigmaOpensDesc X U) K) :=
      morphismProperty_of_isPullback (P := @IsOpenImmersion) (hsq i) inferInstance
    exact isReduced_stalk_of_isOpenImmersion
      (pullback.snd (Sigma.ι (fun i => (U i).toScheme) i)
        (baseChangeProjection (sigmaOpensDesc X U ≫ f) K) ≫
        baseChangeMap f (sigmaOpensDesc X U) K) z
  · intro p
    obtain ⟨i, y, hy⟩ := sigma_jointly_surjective (fun i => (U i).toScheme)
      ((baseChangeProjection (sigmaOpensDesc X U ≫ f) K).base p)
    obtain ⟨z, hz⟩ := exists_pullback_snd_base_eq (Sigma.ι (fun i => (U i).toScheme) i)
      (baseChangeProjection (sigmaOpensDesc X U ≫ f) K) y p hy
    exact ⟨i, z, hz⟩
end FunctorialResolution.EmbeddedResolution
