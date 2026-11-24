-- Prove2me | solution 1 for FunctorialResolution.EmbeddedResolution.OpenImmersionRestriction.false_of_isOpen_preimage_support
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T00:49:45.212279+00:00
-- url     : https://prove2.me/submissions/b2bb8cc8-25a1-40d7-8d52-38c4b8dbcf53

import Mathlib
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_EtaleCoordinates_StrictNormalCrossings
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_DerivativeIdeal_IdealSheafOrder
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_AlgebraicPreliminaries_GenericPointImage
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_IdealPrincipalization_PrincipalizationCertificate
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_StrictTransformIsolation_RestrictionToOpens
import Theorems.Thm_P2M_FunctorialResolution_EmbeddedResolution_OpenImmersionRestriction_isGenericPoint_preimage_subscheme__comp___bf33e8fb56ab
import Theorems.Thm_P2M_FunctorialResolution_EmbeddedResolution_OpenImmersionRestriction_exists_subscheme__comp___apply_eq_of_mem_44f2f59782dc
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_support_comap_eq


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
open FunctorialResolution FunctorialResolution.EmbeddedResolution FunctorialResolution.EmbeddedResolution.OpenImmersionRestriction
namespace FunctorialResolution.EmbeddedResolution.OpenImmersionRestriction
theorem _root_.solution {V : VanishingAssignment.{u}} (hV : IdealSheafGeometryHypotheses V)
    (W : Scheme.{u}) (N Z : W.IdealSheafData) (C : IrreducibleClosedPair W) (U : W.Opens)
    (H : (U.toScheme).IdealSheafData)
    (hptU : C.pt ∈ (U : Set ↥W)) (hptZ : C.pt ∈ (Z.support : Set ↥W))
    (hZH : ((Z.comap U.ι).support : Set ↥(U.toScheme)) ⊆ (H.support : Set ↥(U.toScheme)))
    (hNsubH : ((N.comap U.ι).support : Set ↥(U.toScheme)) ⊆ (H.support : Set ↥(U.toScheme)))
    (hopen : IsOpen (H.subschemeι.base ⁻¹' ((Z.comap U.ι).support : Set ↥(U.toScheme))))
    (hxi2Z : C.xi2 ∉ (Z.support : Set ↥W))
    (hxi2N : C.xi2 ∈ (N.support : Set ↥W)) : False := by
  have hopenU : IsOpen ((U : Set ↥W)) := hV.isOpen_opens W U
  have hxi2U : C.xi2 ∈ (U : Set ↥W) :=
    (C.generic2.mem_open_set_iff hopenU).mpr ⟨C.pt, C.mem_second_closed, hptU⟩
  have hZsub : ⇑U.ι.base ⁻¹' (Z.support : Set ↥W) ⊆ (H.support : Set ↥(U.toScheme)) := by
    rw [← support_comap_eq]
    exact hZH
  have hNsub : ⇑U.ι.base ⁻¹' (N.support : Set ↥W) ⊆ (H.support : Set ↥(U.toScheme)) := by
    rw [← support_comap_eq]
    exact hNsubH
  obtain ⟨y0, hy0⟩ := exists_subschemeι_comp_ι_apply_eq_of_mem hV W U H (Z.support : Set ↥W) hZsub C.pt hptU hptZ
  obtain ⟨y2, hy2⟩ := exists_subschemeι_comp_ι_apply_eq_of_mem hV W U H (N.support : Set ↥W) hNsub C.xi2 hxi2U hxi2N
  have hgen2 : IsGenericPoint y2 ((H.subschemeι ≫ U.ι).base ⁻¹' C.S2) :=
    isGenericPoint_preimage_subschemeι_comp_ι hV W U H C.S2 C.xi2 C.generic2 y2 hy2
  have hclosedA : IsClosed (⇑H.subschemeι.base ⁻¹'
      ((Z.comap U.ι).support : Set ↥(U.toScheme))) :=
    (hV.isClosed_support U.toScheme (Z.comap U.ι)).preimage
      (hV.isClosedEmbedding_subschemeι U.toScheme H).continuous
  have hA : IsClopen (⇑H.subschemeι.base ⁻¹'
      ((Z.comap U.ι).support : Set ↥(U.toScheme))) := ⟨hclosedA, hopen⟩
  have hirr : IsIrreducible ((H.subschemeι ≫ U.ι).base ⁻¹' C.S2) := by
    rw [← hgen2.def]
    exact isIrreducible_singleton.closure
  have hy0A : y0 ∈ ⇑H.subschemeι.base ⁻¹' ((Z.comap U.ι).support : Set ↥(U.toScheme)) := by
    rw [support_comap_eq]
    show U.ι.base (H.subschemeι.base y0) ∈ (Z.support : Set ↥W)
    rw [← hV.base_comp _ _ _ H.subschemeι U.ι y0, hy0]
    exact hptZ
  have hy0S : y0 ∈ (H.subschemeι ≫ U.ι).base ⁻¹' C.S2 := by
    show (H.subschemeι ≫ U.ι).base y0 ∈ C.S2
    rw [hy0]
    exact C.mem_second_closed
  have hsub := hirr.isPreirreducible.isPreconnected.subset_isClopen hA ⟨y0, hy0S, hy0A⟩
  have hy2A : y2 ∈ ⇑H.subschemeι.base ⁻¹' ((Z.comap U.ι).support : Set ↥(U.toScheme)) :=
    hsub hgen2.mem
  apply hxi2Z
  rw [support_comap_eq] at hy2A
  have h' : U.ι.base (H.subschemeι.base y2) ∈ (Z.support : Set ↥W) := hy2A
  rw [← hV.base_comp _ _ _ H.subschemeι U.ι y2, hy2] at h'
  exact h'
end FunctorialResolution.EmbeddedResolution.OpenImmersionRestriction
