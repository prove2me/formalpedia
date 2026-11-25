-- Prove2me | solution 1 for FunctorialResolution.EmbeddedResolution.stalkIdeal_monomialPartAlongDivisor_of_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T02:21:38.443801+00:00
-- url     : https://prove2.me/submissions/7c4b1fc3-ea60-46c1-ab4a-95fc4c41454c

import Mathlib
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_Blowup_BlowupProperties
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_IteratedBlowups_ClopenRestriction
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_StrictTransformCharts_ControlledTransform
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_EtaleCoordinates_CoordinateDivisorSmoothness
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_EtaleCoordinates_ChartRing
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_EtaleCoordinates_EtaleChartExistence
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_EtaleCoordinates_StrictNormalCrossings
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_DerivativeIdeal_IrreducibleComponentsOfSupport
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_DerivativeIdeal_OrderAtGenericPoint
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_DerivativeIdeal_IdealSheafOrder
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_Schemes_AffineOpens
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_Schemes_IdealSheafData
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_IdealPrincipalization_MonomialCase_MonomialSplitting
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_BlowupUniversalProperty
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_ResolutionOfSingularities
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_IdealPrincipalization_MonomialCase_MonomialPartAlongDivisor
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_stalkIdeal_listProd
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_stalkIdeal_componentPowerIdeal_of_not_mem
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_stalkIdeal_componentPowerIdeal_of_mem
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_monomialPartAlongDivisor_eq_inf_componentPowerIdeal
import Theorems.Thm_Derivation_liftToLocalization_algebraMap
import Theorems.Thm_Derivation_mapToLocalization_algebraMap
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_EtaleChart_coordRingHom_X
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_EtaleChart_ofCoords_map
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_EtaleCoordinates_basisDerivation_apply
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_IsIrreducibleComponentOfSupport_disjoint
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_coordVectorInl_inl
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_coordVectorInl_inr
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_coordVectorInr_inl
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_coordVectorInr_inr
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_derivIdealSheafIterate_ideal
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_derivIdealSheafIterate_zero
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_derivIdealSheaf_ideal
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_idealSheafColon_ideal
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_le_iff_forall_stalkIdeal_le
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_pullbackCoord_def
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_stalkIdeal_mono
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_stalkIdeal_mul
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Derivation.liftToLocalization_algebraMap
attribute [local simp] Derivation.mapToLocalization_algebraMap
attribute [local simp] FunctorialResolution.EmbeddedResolution.EtaleChart.coordRingHom_X
attribute [local simp] FunctorialResolution.EmbeddedResolution.EtaleChart.ofCoords_map
attribute [local simp] FunctorialResolution.EmbeddedResolution.EtaleCoordinates.basisDerivation_apply
attribute [local simp] FunctorialResolution.EmbeddedResolution.coordVectorInl_inl
attribute [local simp] FunctorialResolution.EmbeddedResolution.coordVectorInl_inr
attribute [local simp] FunctorialResolution.EmbeddedResolution.coordVectorInr_inl
attribute [local simp] FunctorialResolution.EmbeddedResolution.coordVectorInr_inr
attribute [local simp] FunctorialResolution.EmbeddedResolution.derivIdealSheafIterate_ideal
attribute [local simp] FunctorialResolution.EmbeddedResolution.derivIdealSheafIterate_zero
attribute [local simp] FunctorialResolution.EmbeddedResolution.derivIdealSheaf_ideal
attribute [local simp] FunctorialResolution.EmbeddedResolution.idealSheafColon_ideal
attribute [local simp] FunctorialResolution.EmbeddedResolution.pullbackCoord_def


section
universe u
open CategoryTheory Opposite AlgebraicGeometry TopologicalSpace
noncomputable section
namespace FunctorialResolution.EmbeddedResolution
variable {X : Scheme.{u}}
variable {k : Type u} [Field k]
private theorem idealSheafData_mul_le_left (a b : X.IdealSheafData) : a * b ≤ a := by
  rw [le_iff_forall_stalkIdeal_le]
  intro x
  rw [stalkIdeal_mul]
  exact Ideal.mul_le.mpr fun r hr s _ => Ideal.mul_mem_right s _ hr
private theorem idealSheafData_mul_le_right (a b : X.IdealSheafData) : a * b ≤ b := by
  rw [le_iff_forall_stalkIdeal_le]
  intro x
  rw [stalkIdeal_mul]
  exact Ideal.mul_le.mpr fun r _ s hs => Ideal.mul_mem_left _ r hs
private theorem idealSheafData_listProd_le_of_mem :
    ∀ (L : List X.IdealSheafData) (a : X.IdealSheafData), a ∈ L → L.prod ≤ a := by
  intro L
  induction L with
  | nil =>
      intro a ha
      simp at ha
  | cons b L ih =>
      intro a ha
      rw [List.prod_cons]
      rcases List.mem_cons.mp ha with h | h
      · rw [h]
        exact idealSheafData_mul_le_left _ _
      · exact le_trans (idealSheafData_mul_le_right _ _) (ih a h)
private theorem prod_map_eq_one_of_forall_eq_one {α : Type*} {M : Type*} [CommMonoid M]
    (g : α → M) (L : List α) (h : ∀ b ∈ L, g b = 1) : (L.map g).prod = 1 :=
  List.prod_eq_one fun x hx => by
    obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hx
    exact h a ha
private theorem prod_map_eq_apply_of_nodup_of_forall_ne {α : Type*} {M : Type*} [CommMonoid M]
    (g : α → M) : ∀ (L : List α) (a : α), L.Nodup → a ∈ L →
      (∀ b ∈ L, b ≠ a → g b = 1) → (L.map g).prod = g a := by
  intro L
  induction L with
  | nil =>
      intro a _ ha _
      simp at ha
  | cons b L ih =>
      intro a hnd ha hone
      rw [List.map_cons, List.prod_cons]
      rcases List.mem_cons.mp ha with h | h
      · have hL : (L.map g).prod = 1 := by
          refine prod_map_eq_one_of_forall_eq_one g L ?_
          intro c hc
          refine hone c (List.mem_cons.mpr (Or.inr hc)) ?_
          intro hca
          exact absurd (show b ∈ L by rw [← h, ← hca]; exact hc) (List.nodup_cons.mp hnd).1
        rw [hL, mul_one, h]
      · have hb : g b = 1 := by
          refine hone b (List.mem_cons.mpr (Or.inl rfl)) ?_
          intro hba
          exact absurd (show b ∈ L by rw [hba]; exact h) (List.nodup_cons.mp hnd).1
        rw [hb, one_mul]
        exact ih a (List.nodup_cons.mp hnd).2 h
          (fun c hc => hone c (List.mem_cons.mpr (Or.inr hc)))
end FunctorialResolution.EmbeddedResolution
end
end

set_option autoImplicit false
universe u
open CategoryTheory Opposite AlgebraicGeometry TopologicalSpace
noncomputable section
open FunctorialResolution FunctorialResolution.EmbeddedResolution
variable {X : Scheme.{u}}
variable {k : Type u} [Field k]
namespace FunctorialResolution.EmbeddedResolution
theorem _root_.solution [TopologicalSpace.NoetherianSpace ↥X]
    (p : X ⟶ Spec (CommRingCat.of k)) (I : X.IdealSheafData) {D : X.IdealSheafData}
    (hD : IsEtaleLocallyCoordinateDivisor p D) {C : Set X} (hC : IsIrreducibleComponentOfSupport D C) {x : X}
    (hx : x ∈ C) :
    stalkIdeal (monomialPartAlongDivisor I D) x = stalkIdeal D x ^ orderAlongComponent I hC.isIrreducible := by
  classical
  have hmemiff : ∀ C' : Set X, C' ∈ supportComponentsFinset D ↔ IsIrreducibleComponentOfSupport D C' := by
    intro C'
    simp only [supportComponentsFinset, Set.Finite.mem_toFinset, Set.mem_ofPred_eq]
  have hCS : C ∈ supportComponentsFinset D := (hmemiff C).mpr hC
  have hCpart : stalkIdeal (componentPowerIdeal I D C) x
      = stalkIdeal D x ^ orderAlongComponent I hC.isIrreducible :=
    stalkIdeal_componentPowerIdeal_of_mem p I hD hC hx
  refine le_antisymm ?_ ?_
  · have h1 : monomialPartAlongDivisor I D ≤ componentPowerIdeal I D C := by
      rw [monomialPartAlongDivisor_eq_inf_componentPowerIdeal]
      exact Finset.inf_le hCS
    have h2 := stalkIdeal_mono h1 x
    rwa [hCpart] at h2
  · have hle : ((supportComponentsFinset D).toList.map (fun C' => componentPowerIdeal I D C')).prod
        ≤ monomialPartAlongDivisor I D := by
      rw [monomialPartAlongDivisor_eq_inf_componentPowerIdeal]
      refine Finset.le_inf ?_
      intro C' hC'
      exact idealSheafData_listProd_le_of_mem _ (componentPowerIdeal I D C')
        (List.mem_map.mpr ⟨C', Finset.mem_toList.mpr hC', rfl⟩)
    have hprod : stalkIdeal
        ((supportComponentsFinset D).toList.map (fun C' => componentPowerIdeal I D C')).prod x
        = stalkIdeal (componentPowerIdeal I D C) x := by
      rw [stalkIdeal_listProd, List.map_map]
      refine prod_map_eq_apply_of_nodup_of_forall_ne (fun C' => stalkIdeal (componentPowerIdeal I D C') x)
        ((supportComponentsFinset D).toList) C (Finset.nodup_toList _)
        (Finset.mem_toList.mpr hCS) ?_
      intro C' hC' hne
      show stalkIdeal (componentPowerIdeal I D C') x = 1
      have hC'comp : IsIrreducibleComponentOfSupport D C' := (hmemiff C').mp (Finset.mem_toList.mp hC')
      have hdisj : Disjoint C C' := hC.disjoint hC'comp p hD (Ne.symm hne)
      have hxC' : x ∉ C' := Set.disjoint_left.mp hdisj hx
      rw [stalkIdeal_componentPowerIdeal_of_not_mem I D C' hxC', Ideal.one_eq_top]
    have h3 := stalkIdeal_mono hle x
    rw [hprod, hCpart] at h3
    exact h3
end FunctorialResolution.EmbeddedResolution
