-- Prove2me | solution 1 for FunctorialResolution.EmbeddedResolution.isLocallyGeneratedByNonZeroDivisor_monomialFactorIdeal
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T01:33:57.283272+00:00
-- url     : https://prove2.me/submissions/508d5f4c-e9ad-4ac0-84df-67ec648cbf87

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
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_isEtaleLocallyCoordinateDivisor_of_inStrictNormalCrossingPosition
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_componentPowerIdeal_of_not_isIrreducibleComponentOfSupport
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_componentPowerIdeal_of_isIrreducibleComponentOfSupport
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_monomialPartAlongDivisor_eq_inf_componentPowerIdeal
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_monomialFactorIdeal_eq_prod_monomialPartAlongDivisor
import Theorems.Thm_AlgebraicGeometry_Scheme_exists_affineOpens_mem
import Theorems.Thm_Derivation_liftToLocalization_algebraMap
import Theorems.Thm_Derivation_mapToLocalization_algebraMap
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_EtaleChart_coordRingHom_X
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_EtaleChart_ideal_eq_span_coord
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_EtaleChart_ofCoords_map
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_EtaleCoordinates_basisDerivation_apply
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_IsIrreducibleComponentOfSupport_disjoint
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_IsIrreducibleComponentOfSupport_exists_affineOpen_etaleChart_coordIdeal
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_coordVectorInl_inl
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_coordVectorInl_inr
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_coordVectorInr_inl
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_coordVectorInr_inr
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_coord_mem_nonZeroDivisors
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_derivIdealSheafIterate_ideal
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_derivIdealSheafIterate_zero
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_derivIdealSheaf_ideal
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_idealSheafColon_ideal
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_le_iff_forall_stalkIdeal_le
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_pullbackCoord_def
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_restrictIdeal_eq_restrict_coordIdeal_of_le
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
private theorem idealSheafData_ideal_mul (I J : X.IdealSheafData) (W : X.affineOpens) :
    (I * J).ideal W = I.ideal W * J.ideal W := rfl
private theorem idealSheafData_ideal_top (W : X.affineOpens) :
    (⊤ : X.IdealSheafData).ideal W = ⊤ :=
  (Ideal.eq_top_iff_one _).mpr (by simp)
private theorem idealSheafData_ideal_one (W : X.affineOpens) :
    (1 : X.IdealSheafData).ideal W = 1 := by
  rw [Ideal.one_eq_top]
  exact idealSheafData_ideal_top W
private theorem idealSheafData_ideal_pow (J : X.IdealSheafData) (n : ℕ)
    (W : X.affineOpens) : (J ^ n).ideal W = J.ideal W ^ n := by
  induction n with
  | zero => rw [pow_zero, pow_zero]; exact idealSheafData_ideal_one W
  | succ n ih => rw [pow_succ, pow_succ, idealSheafData_ideal_mul, ih]
private theorem idealSheafData_ideal_listProd (L : List X.IdealSheafData) (W : X.affineOpens) :
    L.prod.ideal W = (L.map (fun J => J.ideal W)).prod := by
  induction L with
  | nil => rw [List.prod_nil, List.map_nil, List.prod_nil]; exact idealSheafData_ideal_one W
  | cons J L ih =>
      rw [List.prod_cons, List.map_cons, List.prod_cons, idealSheafData_ideal_mul, ih]
private theorem ideal_vanishingIdeal_eq_top_of_disjoint (C : Set X) (hCcl : IsClosed C) (W : X.affineOpens)
    (h : ∀ y : X, y ∈ (W : X.Opens) → y ∉ C) :
    (Scheme.IdealSheafData.vanishingIdeal
      (⟨C, hCcl⟩ : TopologicalSpace.Closeds ↥X)).ideal W = ⊤ := by
  refine (Ideal.eq_top_iff_one _).mpr ?_
  rw [Scheme.IdealSheafData.vanishingIdeal_ideal, PrimeSpectrum.mem_vanishingIdeal]
  intro q hq
  have hqC : (W.2.fromSpec).base q ∈ C := hq
  have hmem0 : (W.2.fromSpec).base q ∈ ((W : X.Opens) : Set ↥X) := by
    rw [← AlgebraicGeometry.IsAffineOpen.range_fromSpec W.2]
    exact Set.mem_range_self q
  have hmem : (W.2.fromSpec).base q ∈ (W : X.Opens) := hmem0
  exact absurd hqC (h _ hmem)
private theorem ideal_componentPowerIdeal_eq_top_of_disjoint (I D : X.IdealSheafData) (C : Set X)
    (W : X.affineOpens) (h : ∀ y : X, y ∈ (W : X.Opens) → y ∉ C) :
    (componentPowerIdeal I D C).ideal W = ⊤ := by
  by_cases hC : IsIrreducibleComponentOfSupport D C
  · rw [componentPowerIdeal_of_isIrreducibleComponentOfSupport I D hC, idealSheafData_ideal_pow,
      ideal_vanishingIdeal_eq_top_of_disjoint C hC.isClosed W h, ← Ideal.one_eq_top, one_pow]
  · rw [componentPowerIdeal_of_not_isIrreducibleComponentOfSupport I D hC]
    exact idealSheafData_ideal_top W
private theorem exists_nhds_ideal_monomialPartAlongDivisor_eq_span [TopologicalSpace.NoetherianSpace ↥X]
    (p : X ⟶ Spec (CommRingCat.of k)) (I D : X.IdealSheafData)
    (hD : IsEtaleLocallyCoordinateDivisor p D) (x : X) :
    ∃ Ω : X.Opens, x ∈ Ω ∧ ∀ W : X.affineOpens, (W : X.Opens) ≤ Ω →
      ∃ g ∈ nonZeroDivisors Γ(X, (W : X.Opens)),
        (monomialPartAlongDivisor I D).ideal W = Ideal.span {g} := by
  classical
  have hmemiff : ∀ C' : Set X, C' ∈ supportComponentsFinset D ↔ IsIrreducibleComponentOfSupport D C' := by
    intro C'
    simp only [supportComponentsFinset, Set.Finite.mem_toFinset, Set.mem_ofPred_eq]
  have hprodle : ∀ W : X.affineOpens,
      (((supportComponentsFinset D).toList.map (fun C => componentPowerIdeal I D C)).prod).ideal W
        ≤ (monomialPartAlongDivisor I D).ideal W := by
    intro W
    have hle : ((supportComponentsFinset D).toList.map (fun C => componentPowerIdeal I D C)).prod
        ≤ monomialPartAlongDivisor I D := by
      rw [monomialPartAlongDivisor_eq_inf_componentPowerIdeal]
      refine Finset.le_inf ?_
      intro C' hC'
      exact idealSheafData_listProd_le_of_mem _ (componentPowerIdeal I D C')
        (List.mem_map.mpr ⟨C', Finset.mem_toList.mpr hC', rfl⟩)
    exact hle W
  by_cases hx : ∃ C ∈ supportComponentsFinset D, x ∈ C
  · obtain ⟨C₀, hC₀mem, hxC₀⟩ := hx
    have hC₀ : IsIrreducibleComponentOfSupport D C₀ := (hmemiff C₀).mp hC₀mem
    obtain ⟨V, hV, hxV, n, c, j, hDV, hVsupp, -, hagree, -⟩ :=
      hC₀.exists_affineOpen_etaleChart_coordIdeal p hD x hxC₀
    refine ⟨V, hxV, ?_⟩
    intro W hWV
    refine ⟨(c.restrict hWV).coord j ^ orderAlongComponent I hC₀.isIrreducible,
      pow_mem (coord_mem_nonZeroDivisors W.2 (c.restrict hWV) j) _, ?_⟩
    have hres : restrictIdeal D (W : X.Opens) = (c.restrict hWV).coordIdeal {j} :=
      restrictIdeal_eq_restrict_coordIdeal_of_le hWV c D {j} hDV
    have hDW : D.ideal W = Ideal.span {(c.restrict hWV).coord j} := by
      have h1 := EtaleChart.ideal_eq_span_coord (c.restrict hWV) W.2 D {j} hres
      simpa using h1
    have hcomp0 : (componentPowerIdeal I D C₀).ideal W
        = Ideal.span {(c.restrict hWV).coord j ^ orderAlongComponent I hC₀.isIrreducible} := by
      rw [componentPowerIdeal_of_isIrreducibleComponentOfSupport I D hC₀, idealSheafData_ideal_pow,
        hagree W hWV, hDW, Ideal.span_singleton_pow]
    have hother : ∀ C : Set X, C ∈ (supportComponentsFinset D).toList → C ≠ C₀ →
        (componentPowerIdeal I D C).ideal W = ⊤ := by
      intro C hCmem hne
      have hCcomp : IsIrreducibleComponentOfSupport D C := (hmemiff C).mp (Finset.mem_toList.mp hCmem)
      refine ideal_componentPowerIdeal_eq_top_of_disjoint I D C W ?_
      intro y hy hyC
      have hyV : y ∈ V := hWV hy
      have hyD : y ∈ (D.support : Set X) := hCcomp.subset_support hyC
      have hyC₀ : y ∈ C₀ := hVsupp y hyV hyD
      have hdisj : Disjoint C C₀ := hCcomp.disjoint hC₀ p hD hne
      exact (Set.disjoint_left.mp hdisj hyC) hyC₀
    have hprodideal : (((supportComponentsFinset D).toList.map
        (fun C => componentPowerIdeal I D C)).prod).ideal W = (componentPowerIdeal I D C₀).ideal W := by
      rw [idealSheafData_ideal_listProd, List.map_map]
      refine prod_map_eq_apply_of_nodup_of_forall_ne (fun C => (componentPowerIdeal I D C).ideal W)
        ((supportComponentsFinset D).toList) C₀ (Finset.nodup_toList _)
        (Finset.mem_toList.mpr hC₀mem) ?_
      intro C' hC' hne
      show (componentPowerIdeal I D C').ideal W = 1
      rw [Ideal.one_eq_top]
      exact hother C' hC' hne
    refine le_antisymm ?_ ?_
    · rw [← hcomp0]
      have hle : monomialPartAlongDivisor I D ≤ componentPowerIdeal I D C₀ := by
        rw [monomialPartAlongDivisor_eq_inf_componentPowerIdeal]
        exact Finset.inf_le hC₀mem
      exact hle W
    · rw [← hcomp0, ← hprodideal]
      exact hprodle W
  · push Not at hx
    have hclosed : IsClosed (⋃ C ∈ (supportComponentsFinset D : Set (Set X)), C) := by
      refine Set.Finite.isClosed_biUnion (supportComponentsFinset D).finite_toSet ?_
      intro C hC
      exact ((hmemiff C).mp (Finset.mem_coe.mp hC)).isClosed
    refine ⟨⟨(⋃ C ∈ (supportComponentsFinset D : Set (Set X)), C)ᶜ, hclosed.isOpen_compl⟩, ?_, ?_⟩
    · intro hmem
      rw [Set.mem_iUnion₂] at hmem
      obtain ⟨C, hC, hxC⟩ := hmem
      exact hx C (Finset.mem_coe.mp hC) hxC
    · intro W hWΩ
      refine ⟨1, one_mem _, ?_⟩
      rw [Ideal.span_singleton_one]
      have hall : ∀ C ∈ (supportComponentsFinset D).toList,
          (componentPowerIdeal I D C).ideal W = 1 := by
        intro C hC
        rw [Ideal.one_eq_top]
        refine ideal_componentPowerIdeal_eq_top_of_disjoint I D C W ?_
        intro y hy hyC
        have hyS : y ∈ (⋃ C' ∈ (supportComponentsFinset D : Set (Set X)), C') :=
          Set.mem_biUnion (Finset.mem_coe.mpr (Finset.mem_toList.mp hC)) hyC
        exact absurd hyS (hWΩ hy)
      have hprodtop : (((supportComponentsFinset D).toList.map
          (fun C => componentPowerIdeal I D C)).prod).ideal W = ⊤ := by
        rw [idealSheafData_ideal_listProd, List.map_map, ← Ideal.one_eq_top]
        exact prod_map_eq_one_of_forall_eq_one (fun C => (componentPowerIdeal I D C).ideal W)
          ((supportComponentsFinset D).toList) hall
      refine le_antisymm le_top ?_
      rw [← hprodtop]
      exact hprodle W
private theorem exists_prod_monomialPartAlongDivisor_eq_span_singleton [TopologicalSpace.NoetherianSpace ↥X]
    (p : X ⟶ Spec (CommRingCat.of k)) (I : X.IdealSheafData) (x : X) :
    ∀ L : List X.IdealSheafData, (∀ D ∈ L, IsEtaleLocallyCoordinateDivisor p D) →
      ∃ Ω : X.Opens, x ∈ Ω ∧ ∀ W : X.affineOpens, (W : X.Opens) ≤ Ω →
        ∃ g ∈ nonZeroDivisors Γ(X, (W : X.Opens)),
          ((L.map (fun D => monomialPartAlongDivisor I D)).prod).ideal W = Ideal.span {g} := by
  intro L
  induction L with
  | nil =>
      intro _
      refine ⟨⊤, trivial, ?_⟩
      intro W _
      refine ⟨1, one_mem _, ?_⟩
      rw [List.map_nil, List.prod_nil, Ideal.span_singleton_one]
      exact idealSheafData_ideal_top W
  | cons D L ih =>
      intro hmem
      obtain ⟨Ω₁, hxΩ₁, h₁⟩ := exists_nhds_ideal_monomialPartAlongDivisor_eq_span p I D
        (hmem D (List.mem_cons.mpr (Or.inl rfl))) x
      obtain ⟨Ω₂, hxΩ₂, h₂⟩ := ih (fun D' hD' => hmem D' (List.mem_cons.mpr (Or.inr hD')))
      refine ⟨Ω₁ ⊓ Ω₂, ⟨hxΩ₁, hxΩ₂⟩, ?_⟩
      intro W hW
      obtain ⟨g₁, hg₁, he₁⟩ := h₁ W (le_trans hW inf_le_left)
      obtain ⟨g₂, hg₂, he₂⟩ := h₂ W (le_trans hW inf_le_right)
      refine ⟨g₁ * g₂, mul_mem hg₁ hg₂, ?_⟩
      rw [List.map_cons, List.prod_cons, idealSheafData_ideal_mul, he₁, he₂,
        Ideal.span_singleton_mul_span_singleton]
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
    (p : X ⟶ Spec (CommRingCat.of k)) (E : List X.IdealSheafData) (I : X.IdealSheafData)
    (hE : InStrictNormalCrossingPosition p E) : Blowup.IsLocallyGeneratedByNonZeroDivisor (monomialFactorIdeal E I) := by
  intro x
  obtain ⟨Ω, hxΩ, hΩ⟩ := exists_prod_monomialPartAlongDivisor_eq_span_singleton p I x E
    (fun D hD => isEtaleLocallyCoordinateDivisor_of_inStrictNormalCrossingPosition p E hE D hD)
  obtain ⟨U, hxU⟩ := Scheme.exists_affineOpens_mem x
  have hU : IsAffineOpen (U : X.Opens) := U.2
  obtain ⟨f, hfle, hxf⟩ := hU.exists_basicOpen_le (⟨x, hxΩ⟩ : ↥Ω) hxU
  obtain ⟨g, hg, hgeq⟩ := hΩ (X.affineBasicOpen f) hfle
  refine ⟨X.affineBasicOpen f, g, hxf, hg, ?_⟩
  rw [monomialFactorIdeal_eq_prod_monomialPartAlongDivisor]
  exact hgeq
end FunctorialResolution.EmbeddedResolution
