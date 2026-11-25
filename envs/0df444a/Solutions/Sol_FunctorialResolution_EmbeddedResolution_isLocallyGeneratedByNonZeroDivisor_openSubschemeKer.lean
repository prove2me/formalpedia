-- Prove2me | solution 1 for FunctorialResolution.EmbeddedResolution.isLocallyGeneratedByNonZeroDivisor_openSubschemeKer
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T17:23:42.155408+00:00
-- url     : https://prove2.me/submissions/21b55d6f-6c93-4115-a22b-c3fbf024348f

import Mathlib
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_EtaleCoordinates_StrictNormalCrossings
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_EtaleCoordinates_SmoothRegular
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_AlgebraicPreliminaries_ClopenSubscheme
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_AlgebraicPreliminaries_OpenImmersionAppLE
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_Schemes_SchemeMorphismProperties
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_BlowupUniversalProperty
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_ResolutionOfSingularities
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_EtaleCoordinates_IdealSheafOpenRestriction
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_openSubschemeKer_eq_ker
import Theorems.Thm_P2M_FunctorialResolution_EmbeddedResolution_exists_opens_preimage_subscheme__le_a66fe7f8493c
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_exists_opens_notMem_image
import Theorems.Thm_AlgebraicGeometry_IsOpenImmersion_bijective_appLE_of_image_eq
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_EtaleChart_ofCoords_map
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_coe_complOpensOfIsClosed
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] FunctorialResolution.EmbeddedResolution.EtaleChart.ofCoords_map
attribute [local simp] FunctorialResolution.EmbeddedResolution.coe_complOpensOfIsClosed


section
universe u
open CategoryTheory AlgebraicGeometry TopologicalSpace
noncomputable section
namespace FunctorialResolution.EmbeddedResolution
private theorem image_preimage_opensι_of_le {Y : Scheme.{u}} (V O : Y.Opens) (h : O ≤ V) :
    Scheme.Opens.ι V ''ᵁ (Scheme.Opens.ι V ⁻¹ᵁ O) = O := by
  rw [Scheme.Hom.image_preimage_eq_opensRange_inf]
  refine inf_eq_right.mpr ?_
  intro x hx
  show x ∈ Set.range ⇑(Scheme.Opens.ι V).base
  rw [Scheme.Opens.range_ι]
  exact h hx
private theorem injective_app_opensι_of_le {Y : Scheme.{u}} (V O : Y.Opens) (h : O ≤ V) :
    Function.Injective (CommRingCat.Hom.hom ((Scheme.Opens.ι V).app O)) := by
  have hb := AlgebraicGeometry.IsOpenImmersion.bijective_appLE_of_image_eq (Scheme.Opens.ι V) O
    (Scheme.Opens.ι V ⁻¹ᵁ O) le_rfl (image_preimage_opensι_of_le V O h)
  rw [Scheme.Hom.app_eq_appLE]
  exact hb.1
private theorem subsingleton_sections_of_eq_bot {Y : Scheme.{u}} (V : Y.Opens)
    (hV : V = ⊥) : Subsingleton ↥(Y.presheaf.obj (Opposite.op V)) := by
  have h : CategoryTheory.Limits.IsTerminal (Y.presheaf.obj (Opposite.op V)) :=
    Y.sheaf.isTerminalOfEqEmpty hV
  exact CommRingCat.subsingleton_of_isTerminal h
private theorem ker_app_opensι_comp_subschemeι_eq_of_preimage_le {X : Scheme.{u}} (Z : X.IdealSheafData) (W : Z.subscheme.Opens)
    (V : X.Opens) (hVW : (Z.subschemeι ⁻¹ᵁ V) ≤ W) :
    RingHom.ker (CommRingCat.Hom.hom ((Scheme.Opens.ι W ≫ Z.subschemeι).app V))
      = RingHom.ker (CommRingCat.Hom.hom (Z.subschemeι.app V)) := by
  have hinjW := injective_app_opensι_of_le W (Z.subschemeι ⁻¹ᵁ V) hVW
  ext a
  have hfac : (CommRingCat.Hom.hom ((Scheme.Opens.ι W ≫ Z.subschemeι).app V)) a
      = (CommRingCat.Hom.hom ((Scheme.Opens.ι W).app (Z.subschemeι ⁻¹ᵁ V)))
        ((CommRingCat.Hom.hom (Z.subschemeι.app V)) a) := by
    show (CommRingCat.Hom.hom (Z.subschemeι.app V ≫
      (Scheme.Opens.ι W).app (Z.subschemeι ⁻¹ᵁ V))) a = _
    rw [CommRingCat.hom_comp, RingHom.comp_apply]
  simp only [RingHom.mem_ker, hfac]
  constructor
  · intro ha
    exact hinjW (ha.trans (map_zero _).symm)
  · intro ha
    exact (congrArg _ ha).trans (map_zero _)
private theorem exists_ideal_basicOpen_eq_span_singleton_of_eq_span {X : Scheme.{u}} (J : X.IdealSheafData)
    (U : X.affineOpens) (s f : Γ(X, U.1)) (hf : f ∈ nonZeroDivisors Γ(X, U.1))
    (hJ : J.ideal U = Ideal.span {f}) :
    ∃ f' : Γ(X, X.basicOpen s), f' ∈ nonZeroDivisors Γ(X, X.basicOpen s) ∧
      J.ideal ⟨X.basicOpen s, U.2.basicOpen s⟩ = Ideal.span {f'} := by
  have hmap := J.map_ideal_basicOpen U s
  rw [hJ, Ideal.map_span, Set.image_singleton] at hmap
  have := U.2.isLocalization_basicOpen s
  refine ⟨_, ?_, hmap.symm⟩
  exact IsLocalization.nonZeroDivisors_le_comap (Submonoid.powers s) Γ(X, X.basicOpen s) hf
private theorem one_eq_zero_sections_of_eq_bot {Y : Scheme.{u}} (V : Y.Opens) (hV : V = ⊥) :
    (1 : Γ(Y, V)) = 0 := by
  have := subsingleton_sections_of_eq_bot V hV
  exact Subsingleton.elim _ _
end FunctorialResolution.EmbeddedResolution
end
end

set_option autoImplicit false
universe u
open CategoryTheory AlgebraicGeometry TopologicalSpace
noncomputable section
open FunctorialResolution FunctorialResolution.EmbeddedResolution
namespace FunctorialResolution.EmbeddedResolution
theorem _root_.solution {X : Scheme.{u}} (Z : X.IdealSheafData)
    (W : Z.subscheme.Opens) (hW : IsClosed (W : Set Z.subscheme))
    (hZ : Blowup.IsLocallyGeneratedByNonZeroDivisor Z) : Blowup.IsLocallyGeneratedByNonZeroDivisor (openSubschemeKer Z W) := by
  have hindW : Topology.IsInducing ⇑(Scheme.Opens.ι W).base :=
    (Scheme.Opens.ι W).isEmbedding.toIsInducing
  have hrangeW : Set.range ⇑(Scheme.Opens.ι W).base = (W : Set Z.subscheme) := by
    rw [Scheme.Opens.range_ι]
  have hqcW : QuasiCompact (Scheme.Opens.ι W) := by
    refine ⟨fun U _ hUc => ?_⟩
    refine hindW.isCompact_iff.mpr ?_
    rw [Set.image_preimage_eq_inter_range, hrangeW]
    exact hUc.inter_right hW
  have hqc : QuasiCompact (Scheme.Opens.ι W ≫ Z.subschemeι) := inferInstance
  have hpiece : ∀ V : X.affineOpens, (Z.subschemeι ⁻¹ᵁ V.1) ≤ W →
      (openSubschemeKer Z W).ideal V = Z.ideal V := by
    intro V hVW
    have h2 : RingHom.ker (CommRingCat.Hom.hom (Z.subschemeι.app V.1)) = Z.ideal V := by
      rw [← AlgebraicGeometry.Scheme.Hom.ker_apply Z.subschemeι V,
        Scheme.IdealSheafData.ker_subschemeι]
    rw [openSubschemeKer_eq_ker, AlgebraicGeometry.Scheme.Hom.ker_apply, ker_app_opensι_comp_subschemeι_eq_of_preimage_le Z W V.1 hVW, h2]
  have hpiecetop : ∀ V : X.affineOpens,
      ((Scheme.Opens.ι W ≫ Z.subschemeι) ⁻¹ᵁ V.1) = ⊥ → (openSubschemeKer Z W).ideal V = ⊤ := by
    intro V hbot
    rw [openSubschemeKer_eq_ker, AlgebraicGeometry.Scheme.Hom.ker_apply, Ideal.eq_top_iff_one,
      RingHom.mem_ker, map_one]
    exact one_eq_zero_sections_of_eq_bot _ hbot
  intro x
  by_cases hx : x ∈ ⇑Z.subschemeι.base '' (W : Set Z.subscheme)
  · obtain ⟨N, hxN, hNle⟩ := exists_opens_preimage_subschemeι_le Z W x hx
    obtain ⟨U₁, f₁, hxU₁, hf₁, hZU₁⟩ := hZ x
    have hU₁ : IsAffineOpen U₁.1 := U₁.2
    obtain ⟨s, hsN, hxs⟩ := hU₁.exists_basicOpen_le (⟨x, hxN⟩ : ↥N) hxU₁
    obtain ⟨f, hf, hZU⟩ := exists_ideal_basicOpen_eq_span_singleton_of_eq_span Z U₁ s f₁ hf₁ hZU₁
    have hVW : (Z.subschemeι ⁻¹ᵁ (X.basicOpen s)) ≤ W := fun v hv => hNle (hsN hv)
    refine ⟨⟨X.basicOpen s, hU₁.basicOpen s⟩, f, hxs, hf, ?_⟩
    exact (hpiece ⟨X.basicOpen s, hU₁.basicOpen s⟩ hVW).trans hZU
  · obtain ⟨N, hxN, hNno⟩ := exists_opens_notMem_image Z W hW x hx
    obtain ⟨U₀, hxU₀⟩ : ∃ U₀ : X.affineOpens, x ∈ U₀.1 := by
      have hx' : x ∈ (⊤ : X.Opens) := Set.mem_univ x
      rw [← iSup_affineOpens_eq_top X] at hx'
      obtain ⟨U₀, hU₀⟩ := Opens.mem_iSup.mp hx'
      exact ⟨U₀, hU₀⟩
    have hU₀ : IsAffineOpen U₀.1 := U₀.2
    obtain ⟨s, hsN, hxs⟩ := hU₀.exists_basicOpen_le (⟨x, hxN⟩ : ↥N) hxU₀
    refine ⟨⟨X.basicOpen s, hU₀.basicOpen s⟩, 1, hxs, one_mem _, ?_⟩
    have hbot : (Scheme.Opens.ι W ≫ Z.subschemeι) ⁻¹ᵁ (X.basicOpen s) = ⊥ := by
      refine le_antisymm ?_ bot_le
      intro w hw
      have hw2 : Z.subschemeι.base ((Scheme.Opens.ι W).base w) ∈ X.basicOpen s := hw
      have hmem : (Scheme.Opens.ι W).base w ∈ (W : Set Z.subscheme) := by
        rw [← Scheme.Opens.range_ι W]
        exact ⟨w, rfl⟩
      exact absurd (hsN hw2) (hNno _ hmem)
    rw [Ideal.span_singleton_one]
    exact hpiecetop ⟨X.basicOpen s, hU₀.basicOpen s⟩ hbot
end FunctorialResolution.EmbeddedResolution
