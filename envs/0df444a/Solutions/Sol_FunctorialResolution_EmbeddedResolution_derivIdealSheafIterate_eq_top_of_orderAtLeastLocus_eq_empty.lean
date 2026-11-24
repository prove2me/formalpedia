-- Prove2me | solution 1 for FunctorialResolution.EmbeddedResolution.derivIdealSheafIterate_eq_top_of_orderAtLeastLocus_eq_empty
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T16:07:12.018788+00:00
-- url     : https://prove2.me/submissions/34ba60ab-20a8-4623-acbc-44acc1ea4a2e

import Mathlib
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_EtaleCoordinates_LocalParameters
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_DerivativeIdeal_DerivativeIdeal
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_DerivativeIdeal_DerivativeIdealLocalization
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_DerivativeIdeal_DerivativeIdealSheaf
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_DerivativeIdeal_IdealOrder
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_DerivativeIdeal_IdealSheafOrder
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_DerivativeIdeal_DerivativeIdealOrderDecrease
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_DerivativeIdeal_DerivativeIdealSheafOrderDecrease
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_support_derivIdealSheafIterate_eq_orderAtLeastLocus
import Theorems.Thm_Derivation_liftToLocalization_algebraMap
import Theorems.Thm_Derivation_mapToLocalization_algebraMap
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_derivIdealSheafIterate_ideal
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_derivIdealSheafIterate_zero
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_derivIdealSheaf_ideal
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_mem_support_iff_stalkIdeal_le_maximalIdeal
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_stalkIdeal_eq_map_germ
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Derivation.liftToLocalization_algebraMap
attribute [local simp] Derivation.mapToLocalization_algebraMap
attribute [local simp] FunctorialResolution.EmbeddedResolution.derivIdealSheafIterate_ideal
attribute [local simp] FunctorialResolution.EmbeddedResolution.derivIdealSheafIterate_zero
attribute [local simp] FunctorialResolution.EmbeddedResolution.derivIdealSheaf_ideal


section
universe u
open AlgebraicGeometry CategoryTheory TopologicalSpace
namespace FunctorialResolution.EmbeddedResolution
private theorem ideal_eq_top_of_support_eq_empty {X : Scheme.{u}} (J : X.IdealSheafData)
    (hJ : (J.support : Set X) = (∅ : Set X)) (U : X.affineOpens) :
    J.ideal U = ⊤ := by
  have hcover : (⨆ f : (J.ideal U : Set Γ(X, U.1)), X.basicOpen (f : Γ(X, U.1))) = U.1 := by
    refine le_antisymm (iSup_le fun f => X.basicOpen_le (f : Γ(X, U.1))) ?_
    rw [SetLike.le_def]
    intro x hxU
    have hxs : x ∉ J.support := by
      intro hc
      have hmem : x ∈ (J.support : Set X) := hc
      rw [hJ] at hmem
      simp at hmem
    have hnle : ¬ stalkIdeal J x ≤ IsLocalRing.maximalIdeal (X.presheaf.stalk x) := fun hc =>
      hxs ((mem_support_iff_stalkIdeal_le_maximalIdeal J x).mpr hc)
    rw [stalkIdeal_eq_map_germ J x U hxU, Ideal.map_le_iff_le_comap,
      SetLike.not_le_iff_exists] at hnle
    obtain ⟨a, ha, ha2⟩ := hnle
    have hbo : x ∈ X.basicOpen a := by
      refine (X.mem_basicOpen a x hxU).mpr ?_
      by_contra hc
      exact ha2 (Ideal.mem_comap.mpr ((IsLocalRing.mem_maximalIdeal _).mpr
        (mem_nonunits_iff.mpr hc)))
    exact Opens.mem_iSup.mpr ⟨⟨a, ha⟩, hbo⟩
  have hspan := (IsAffineOpen.iSup_basicOpen_eq_self_iff U.2).mp hcover
  rwa [Ideal.span_eq] at hspan
end FunctorialResolution.EmbeddedResolution
end

set_option autoImplicit false
universe u
open AlgebraicGeometry CategoryTheory TopologicalSpace
open FunctorialResolution FunctorialResolution.EmbeddedResolution
namespace FunctorialResolution.EmbeddedResolution
theorem _root_.solution (k : Type u) [Field k] [CharZero k] {X : Scheme.{u}}
    (p : X ⟶ Spec (CommRingCat.of k)) [AlgebraicGeometry.Smooth p] (I : X.IdealSheafData)
    (m : ℕ) (h : orderAtLeastLocus I (m + 1) = (∅ : Set X)) :
    derivIdealSheafIterate k p m I = ⊤ := by
  have hsupp : ((derivIdealSheafIterate k p m I).support : Set X) = (∅ : Set X) := by
    have h2 := support_derivIdealSheafIterate_eq_orderAtLeastLocus k p I (m := m + 1) (Nat.le_add_left 1 m)
    simp only [Nat.add_sub_cancel] at h2
    exact h2.trans h
  refine le_antisymm le_top ?_
  intro U
  rw [ideal_eq_top_of_support_eq_empty (derivIdealSheafIterate k p m I) hsupp U]
  exact le_top
end FunctorialResolution.EmbeddedResolution
