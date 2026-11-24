-- Prove2me | solution 1 for FunctorialResolution.EmbeddedResolution.OpenImmersionRestriction.false_of_smoothOrderOneCentersIsolated_opens
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T12:02:33.6208+00:00
-- url     : https://prove2.me/submissions/4c3aaa33-973e-49ab-abe9-b10169b20bf6

import Mathlib
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_EtaleCoordinates_StrictNormalCrossings
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_DerivativeIdeal_IdealSheafOrder
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_AlgebraicPreliminaries_GenericPointImage
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_StrictTransformIsolation_RestrictionToOpens
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_IdealPrincipalization_PrincipalizationCertificate
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_StrictTransformIsolation_SmoothOrderOneCenters
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_closure_inter_open_eq
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_isGenericPoint_preimage_of_isInducing
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_isIrreducible_inter_open
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_isIrreducible_preimage_of_isEmbedding
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_one_le_orderAt_iff_mem_support

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
namespace FunctorialResolution.EmbeddedResolution.OpenImmersionRestriction
private theorem irreducibleComponents_opens_not_subset_preimage {V : VanishingAssignment.{u}} (hV : IdealSheafGeometryHypotheses V)
    (W : Scheme.{u}) (U : W.Opens) (T : Set ↥W) (hT : IsClosed T)
    (hcomp : ∀ E ∈ irreducibleComponents ↥W, ¬ E ⊆ T) :
    ∀ E ∈ irreducibleComponents ↥(U.toScheme), ¬ E ⊆ U.ι.base ⁻¹' T := by
  intro E hE hsub
  have hEirr : IsIrreducible E := hE.1
  have hrange := hV.range_ι W U
  have hcont : Continuous ⇑U.ι.base := (hV.isEmbedding_ι W U).continuous
  have hmemU : ∀ y : ↥(U.toScheme), U.ι.base y ∈ (U : Set ↥W) := by
    intro y
    rw [← hrange]
    exact Set.mem_range_self y
  obtain ⟨y0, hy0⟩ := hEirr.nonempty
  have himg : IsIrreducible (U.ι.base '' E) := hEirr.image _ hcont.continuousOn
  obtain ⟨Zc, hZpre, hAZ, hZmax⟩ :=
    exists_preirreducible (closure (U.ι.base '' E)) himg.closure.2
  have hZirr : IsIrreducible Zc := ⟨himg.closure.1.mono hAZ, hZpre⟩
  have hZmem : Zc ∈ irreducibleComponents ↥W :=
    ⟨hZirr, fun u hu hZu => (hZmax u hu.2 hZu).le⟩
  have hEZ : E ⊆ U.ι.base ⁻¹' Zc := by
    intro y hy
    exact hAZ (subset_closure ⟨y, hy, rfl⟩)
  have hZU : (Zc ∩ (U : Set ↥W)).Nonempty := ⟨U.ι.base y0, hEZ hy0, hmemU y0⟩
  have hZUirr : IsIrreducible (Zc ∩ (U : Set ↥W)) :=
    FunctorialResolution.EmbeddedResolution.isIrreducible_inter_open hZirr (hV.isOpen_opens W U) hZU
  have hsubr : (Zc ∩ (U : Set ↥W)) ⊆ Set.range ⇑U.ι.base := by
    rw [hrange]
    exact Set.inter_subset_right
  have hPirr : IsIrreducible (U.ι.base ⁻¹' (Zc ∩ (U : Set ↥W))) :=
    FunctorialResolution.EmbeddedResolution.isIrreducible_preimage_of_isEmbedding (hV.isEmbedding_ι W U) hZUirr hsubr
  have hPeq : U.ι.base ⁻¹' (Zc ∩ (U : Set ↥W)) = U.ι.base ⁻¹' Zc := by
    ext y
    constructor
    · intro hy
      exact hy.1
    · intro hy
      exact ⟨hy, hmemU y⟩
  rw [hPeq] at hPirr
  have hpreimageSub : U.ι.base ⁻¹' Zc ⊆ E := hE.2 hPirr hEZ
  have hZT : Zc ∩ (U : Set ↥W) ⊆ T := by
    rintro x ⟨hxZ, hxU⟩
    rw [← hrange] at hxU
    obtain ⟨y, rfl⟩ := hxU
    exact hsub (hpreimageSub hxZ)
  have hZcl : IsClosed Zc := isClosed_of_mem_irreducibleComponents Zc hZmem
  refine hcomp Zc hZmem ?_
  rw [← FunctorialResolution.EmbeddedResolution.closure_inter_open_eq hZcl hZirr (hV.isOpen_opens W U) hZU]
  exact closure_minimal hZT hT
end FunctorialResolution.EmbeddedResolution.OpenImmersionRestriction
end

set_option autoImplicit false
universe u
open CategoryTheory AlgebraicGeometry TopologicalSpace
open FunctorialResolution FunctorialResolution.EmbeddedResolution FunctorialResolution.EmbeddedResolution.OpenImmersionRestriction
namespace FunctorialResolution.EmbeddedResolution.OpenImmersionRestriction
theorem _root_.solution {V : VanishingAssignment.{u}} (hV : IdealSheafGeometryHypotheses V)
    (hG : SmoothVanishingHypotheses V) {k : Type u} [Field k] [CharZero k] {W : Scheme.{u}}
    (p : W ⟶ Spec (CommRingCat.of k)) (I Z : W.IdealSheafData) (m : ℕ) (Mem : Set ↥W)
    (C : PointedIrreducibleClosed W) (U : W.Opens) (hptU : C.pt ∈ (U : Set ↥W))
    (hIso : SmoothOrderOneCentersIsolated V U.toScheme (U.ι ≫ p) (I.comap U.ι) m
      (U.ι.base ⁻¹' Mem) (Z.comap U.ι))
    (hp : Smooth p) (hm : m = 1)
    (hsm : Smooth ((V W ⟨C.S, C.closedS⟩).subschemeι ≫ p))
    (hcomp : ∀ E ∈ irreducibleComponents ↥W, ¬ E ⊆ C.S)
    (hxi : C.xi ∉ (Z.support : Set ↥W))
    (hdisj : Disjoint C.S Mem)
    (hagree : ∀ x ∈ C.S, AgreeNear I (V W ⟨C.S, C.closedS⟩) x)
    (hpt : C.pt ∈ (Z.support : Set ↥W)) : False := by
  have hcont : Continuous ⇑U.ι.base := (hV.isEmbedding_ι W U).continuous
  have hrange := hV.range_ι W U
  have hxiU : C.xi ∈ (U : Set ↥W) :=
    (C.genericXi.mem_open_set_iff (hV.isOpen_opens W U)).mpr ⟨C.pt, C.memPt, hptU⟩
  have hxiR : C.xi ∈ Set.range ⇑U.ι.base := by
    rw [hrange]
    exact hxiU
  have hptR : C.pt ∈ Set.range ⇑U.ι.base := by
    rw [hrange]
    exact hptU
  obtain ⟨y0, hy0⟩ := hxiR
  obtain ⟨y1, hy1⟩ := hptR
  have hS'closed : IsClosed (U.ι.base ⁻¹' C.S) := C.closedS.preimage hcont
  have hgen' : IsGenericPoint y0 (U.ι.base ⁻¹' C.S) :=
    FunctorialResolution.EmbeddedResolution.isGenericPoint_preimage_of_isInducing (hV.isEmbedding_ι W U).toIsInducing
      C.genericXi hy0
  have hirr' : IsIrreducible (U.ι.base ⁻¹' C.S) := by
    rw [← hgen']
    exact isIrreducible_singleton.closure
  have hmemPt : y1 ∈ U.ι.base ⁻¹' C.S := by
    show U.ι.base y1 ∈ C.S
    rw [hy1]
    exact C.memPt
  refine hIso ⟨U.ι.base ⁻¹' C.S, y0, y1, hS'closed, hirr', hgen', hmemPt⟩
    (hG.smooth_opens_ι_comp k W p U hp) hm
    (hG.smooth_vanishing_opens k W p U ⟨C.S, C.closedS⟩ ⟨U.ι.base ⁻¹' C.S, hS'closed⟩ rfl hsm)
    (irreducibleComponents_opens_not_subset_preimage hV W U C.S C.closedS hcomp) ?_ ?_ ?_ ?_
  · intro hmem
    apply hxi
    have h1 : (1 : ℕ∞) ≤ orderAt (Z.comap U.ι) y0 :=
      (one_le_orderAt_iff_mem_support (Z.comap U.ι) y0).mpr hmem
    rw [hV.orderAt_comap W U Z y0, hy0] at h1
    exact (one_le_orderAt_iff_mem_support Z C.xi).mp h1
  · rw [Set.disjoint_left]
    intro y hy hy2
    exact (Set.disjoint_left.mp hdisj hy) hy2
  · intro y hy
    have h1 := hV.agreeNear_comap W U I (V W ⟨C.S, C.closedS⟩) y (hagree _ hy)
    rw [hV.comap_vanishing W ⟨C.S, C.closedS⟩ U ⟨U.ι.base ⁻¹' C.S, hS'closed⟩ rfl] at h1
    exact h1
  · have h1 : (1 : ℕ∞) ≤ orderAt Z C.pt := (one_le_orderAt_iff_mem_support Z C.pt).mpr hpt
    rw [← hy1, ← hV.orderAt_comap W U Z y1] at h1
    exact (one_le_orderAt_iff_mem_support (Z.comap U.ι) y1).mp h1
end FunctorialResolution.EmbeddedResolution.OpenImmersionRestriction
