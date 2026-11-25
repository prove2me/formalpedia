-- Prove2me | solution 1 for FunctorialResolution.EmbeddedResolution.exists_isMonomialSplitting
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T17:44:09.163899+00:00
-- url     : https://prove2.me/submissions/aaa7c144-097f-45c0-bd2c-1d7002f708f8

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
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_coe_orderAlongComponent_eq_orderAt_genericPoint
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_componentPowerIdeal_of_not_isIrreducibleComponentOfSupport
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_componentPowerIdeal_of_isIrreducibleComponentOfSupport
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_monomialPartAlongDivisor_eq_inf_componentPowerIdeal
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_stalkIdeal_monomialPartAlongDivisor_of_not_mem_support
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_stalkIdeal_monomialPartAlongDivisor_of_mem
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_monomialFactorIdeal_eq_prod_monomialPartAlongDivisor
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_stalkIdeal_monomialFactorIdeal
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_monomialFactorIdeal_mul_nonMonomialFactorIdeal
import Theorems.Thm_AlgebraicGeometry_Scheme_IdealSheafData_comap_ideal_eq_map_appLE
import Theorems.Thm_P2M_RH_AlgebraicGeometry_Scheme_IdealSheafData_comap_mul_ffd4b47c5064b9ee
import Theorems.Thm_AlgebraicGeometry_Scheme_IdealSheafData_comap_pow
import Theorems.Thm_Derivation_liftToLocalization_algebraMap
import Theorems.Thm_Derivation_mapToLocalization_algebraMap
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_EtaleChart_coordRingHom_X
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_EtaleChart_ideal_eq_span_coord
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_EtaleChart_ofCoords_map
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_EtaleCoordinates_basisDerivation_apply
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_HasStrictNormalCrossingsWith_exists_etaleChart
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_InStrictNormalCrossingPositionAt_exists_etaleChart
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_IsIrreducibleComponentOfSupport_disjoint
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_IsIrreducibleComponentOfSupport_exists_affineOpen_etaleChart_coordIdeal
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_IsIrreducibleComponentOfSupport_genericPoint_mem
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_IsIrreducibleComponentOfSupport_genericPoint_mem_support
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_coordVectorInl_inl
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_coordVectorInl_inr
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_coordVectorInr_inl
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_coordVectorInr_inr
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_derivIdealSheafIterate_ideal
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_derivIdealSheafIterate_zero
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_derivIdealSheaf_ideal
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_exists_etaleChart
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_idealSheafColon_ideal
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_inStrictNormalCrossingPosition_iff
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_le_iff_forall_stalkIdeal_le
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_le_orderAt_iff
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_mem_span_coord_of_coord_mul_mem
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_mem_support_iff_stalkIdeal_le_maximalIdeal
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_mem_support_iff_stalkIdeal_ne_top
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_notMem_support_of_mem_opens_of_restrictIdeal_eq_top
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_pullbackCoord_def
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_restrictIdeal_eq_restrict_coordIdeal_of_le
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_stalkIdeal_eq_span_germ_coord
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_stalkIdeal_genericPoint_eq_maximalIdeal
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
private theorem prod_map_eq_apply_getElem_of_forall_ne {α : Type*} {M : Type*} [CommMonoid M] (g : α → M) :
    ∀ (L : List α) (i : ℕ) (hi : i < L.length),
      (∀ (j : ℕ) (hj : j < L.length), j ≠ i → g L[j] = 1) → (L.map g).prod = g L[i] := by
  intro L
  induction L with
  | nil =>
      intro i hi
      exact absurd hi (by simp only [List.length_nil]; omega)
  | cons b L ih =>
      intro i hi hone
      cases i with
      | zero =>
          have h1 : (L.map g).prod = 1 := by
            refine prod_map_eq_one_of_forall_eq_one g L ?_
            intro y hy
            obtain ⟨j, hj, hjy⟩ := List.getElem_of_mem hy
            have h2 := hone (j + 1) (by simp only [List.length_cons]; omega) (by omega)
            rw [← hjy]
            simpa using h2
          show (List.map g (b :: L)).prod = g b
          rw [List.map_cons, List.prod_cons, h1, mul_one]
      | succ i =>
          have hi' : i < L.length := by
            simp only [List.length_cons] at hi
            omega
          have hb : g b = 1 := by
            have h0 := hone 0 (by simp only [List.length_cons]; omega) (by omega)
            simpa using h0
          have hrest : (L.map g).prod = g L[i] := by
            refine ih i hi' ?_
            intro j hj hji
            have h2 := hone (j + 1) (by simp only [List.length_cons]; omega) (by omega)
            simpa using h2
          show (List.map g (b :: L)).prod = g L[i]
          rw [List.map_cons, List.prod_cons, hb, one_mul]
          exact hrest
private theorem not_mem_support_of_stalkIdeal_eq_maximalIdeal (p : X ⟶ Spec (CommRingCat.of k))
    {V : X.Opens} (hV : IsAffineOpen V) {m : ℕ} (c : EtaleChart p V m)
    {D D' : X.IdealSheafData} {t s : Fin m} (hts : t ≠ s)
    (hDV : restrictIdeal D V = c.coordIdeal {t})
    (hD'V : restrictIdeal D' V = c.coordIdeal {s})
    {x : ↥X} (hx : x ∈ V)
    (hmax : stalkIdeal D x = IsLocalRing.maximalIdeal (X.presheaf.stalk x))
    (hxD' : x ∈ D'.support) : False := by
  classical
  have hDspan : stalkIdeal D x =
      Ideal.span ({(X.presheaf.germ V x hx).hom (c.coord t)} : Set (X.presheaf.stalk x)) :=
    stalkIdeal_eq_span_germ_coord p hV c t D hDV x hx
  have hD'span : stalkIdeal D' x =
      Ideal.span ({(X.presheaf.germ V x hx).hom (c.coord s)} : Set (X.presheaf.stalk x)) :=
    stalkIdeal_eq_span_germ_coord p hV c s D' hD'V x hx
  have hle : stalkIdeal D' x ≤ IsLocalRing.maximalIdeal (X.presheaf.stalk x) :=
    (mem_support_iff_stalkIdeal_le_maximalIdeal D' x).mp hxD'
  have hmem : (X.presheaf.germ V x hx).hom (c.coord s) ∈ stalkIdeal D x := by
    rw [hmax]
    refine hle ?_
    rw [hD'span]
    exact Ideal.mem_span_singleton_self _
  rw [hDspan, Ideal.mem_span_singleton'] at hmem
  obtain ⟨g, hg⟩ := hmem
  let : Algebra Γ(X, V) (X.presheaf.stalk x) := (X.presheaf.germ V x hx).hom.toAlgebra
  have hlocz : IsLocalization (hV.primeIdealOf ⟨x, hx⟩).asIdeal.primeCompl
      (X.presheaf.stalk x) := hV.isLocalization_stalk ⟨x, hx⟩
  have halg : (algebraMap Γ(X, V) (X.presheaf.stalk x)) = (X.presheaf.germ V x hx).hom := rfl
  obtain ⟨w, hw⟩ := IsLocalization.surj
    (M := (hV.primeIdealOf ⟨x, hx⟩).asIdeal.primeCompl) g
  have hw' : g * (X.presheaf.germ V x hx).hom (w.2 : Γ(X, V))
      = (X.presheaf.germ V x hx).hom w.1 := by
    rw [← halg]
    exact hw
  have heq : (algebraMap Γ(X, V) (X.presheaf.stalk x)) ((w.2 : Γ(X, V)) * c.coord s)
      = (algebraMap Γ(X, V) (X.presheaf.stalk x)) (w.1 * c.coord t) := by
    rw [map_mul, map_mul, halg, ← hg, ← hw']
    ring
  obtain ⟨v, hv⟩ : ∃ v : (hV.primeIdealOf ⟨x, hx⟩).asIdeal.primeCompl,
      (v : Γ(X, V)) * ((w.2 : Γ(X, V)) * c.coord s)
        = (v : Γ(X, V)) * (w.1 * c.coord t) :=
    (IsLocalization.eq_iff_exists (M := (hV.primeIdealOf ⟨x, hx⟩).asIdeal.primeCompl)
      (S := X.presheaf.stalk x)).mp heq
  have hspan : ((v : Γ(X, V)) * (w.2 : Γ(X, V))) ∈ Ideal.span ({c.coord t} : Set Γ(X, V)) := by
    refine mem_span_coord_of_coord_mul_mem hV c hts ((v : Γ(X, V)) * (w.2 : Γ(X, V))) ?_
    have hmul : c.coord s * ((v : Γ(X, V)) * (w.2 : Γ(X, V)))
        = ((v : Γ(X, V)) * w.1) * c.coord t := by linear_combination hv
    rw [hmul]
    exact Ideal.mem_span_singleton'.mpr ⟨(v : Γ(X, V)) * w.1, rfl⟩
  have hunit : IsUnit ((X.presheaf.germ V x hx).hom ((v : Γ(X, V)) * (w.2 : Γ(X, V)))) := by
    rw [← halg, map_mul]
    exact (IsLocalization.map_units (X.presheaf.stalk x) v).mul
      (IsLocalization.map_units (X.presheaf.stalk x) w.2)
  have hfin : (X.presheaf.germ V x hx).hom ((v : Γ(X, V)) * (w.2 : Γ(X, V)))
      ∈ IsLocalRing.maximalIdeal (X.presheaf.stalk x) := by
    rw [← hmax, hDspan]
    obtain ⟨z, hz⟩ := Ideal.mem_span_singleton'.mp hspan
    refine Ideal.mem_span_singleton'.mpr ⟨(X.presheaf.germ V x hx).hom z, ?_⟩
    rw [← map_mul, hz]
  exact (mem_nonunits_iff.mp ((IsLocalRing.mem_maximalIdeal _).mp hfin)) hunit
private theorem stalkIdeal_monomialFactorIdeal_genericPoint [TopologicalSpace.NoetherianSpace ↥X]
    (p : X ⟶ Spec (CommRingCat.of k)) (E : List X.IdealSheafData) (I : X.IdealSheafData)
    (hE : InStrictNormalCrossingPosition p E) {D : X.IdealSheafData} (hD : D ∈ E) {C : Set X}
    (hC : IsIrreducibleComponentOfSupport D C) :
    stalkIdeal (monomialFactorIdeal E I) hC.isIrreducible.genericPoint =
      stalkIdeal D hC.isIrreducible.genericPoint ^ orderAlongComponent I hC.isIrreducible := by
  classical
  obtain ⟨i0, hi0, hi0D⟩ := List.getElem_of_mem hD
  have hloc : IsEtaleLocallyCoordinateDivisor p D := isEtaleLocallyCoordinateDivisor_of_inStrictNormalCrossingPosition p E hE D hD
  obtain ⟨-, hpos⟩ := (inStrictNormalCrossingPosition_iff p E).mp hE
  obtain ⟨U, hηU, m, c, a, hinj, hnone, hsome⟩ :=
    InStrictNormalCrossingPositionAt.exists_etaleChart (hpos hC.isIrreducible.genericPoint)
  have hmaxD : stalkIdeal D hC.isIrreducible.genericPoint
      = IsLocalRing.maximalIdeal (X.presheaf.stalk hC.isIrreducible.genericPoint) :=
    stalkIdeal_genericPoint_eq_maximalIdeal p D hloc hC.isIrreducible hC.subset_support hC.maximal
  have hηD : hC.isIrreducible.genericPoint ∈ D.support := hC.genericPoint_mem_support
  obtain ⟨t, hat⟩ : ∃ t : Fin m, a i0 = some t := by
    cases hai : a i0 with
    | none =>
        refine absurd hηD (notMem_support_of_mem_opens_of_restrictIdeal_eq_top D U ?_ _ hηU)
        rw [← hi0D]
        exact hnone i0 hi0 hai
    | some t =>
        refine ⟨t, ?_⟩
        simp
  have hDU : restrictIdeal D U = c.coordIdeal {t} := by
    rw [← hi0D]
    exact hsome i0 hi0 t hat
  have hother : ∀ (j : ℕ) (hj : j < E.length), j ≠ i0 →
      hC.isIrreducible.genericPoint ∉ (E[j].support : Set ↥X) := by
    intro j hj hji0 hmem
    cases haj : a j with
    | none =>
        exact notMem_support_of_mem_opens_of_restrictIdeal_eq_top E[j] U (hnone j hj haj) _ hηU hmem
    | some s =>
        have hts : t ≠ s := by
          intro h
          exact hji0 (hinj j hj i0 hi0 t (by rw [haj, h]) hat)
        have hmem' : hC.isIrreducible.genericPoint ∈ E[j].support := hmem
        have hxtop : hC.isIrreducible.genericPoint ∈ (⨆ W : X.affineOpens, (W : X.Opens)) := by
          rw [AlgebraicGeometry.iSup_affineOpens_eq_top X]
          trivial
        obtain ⟨W, hηW⟩ := TopologicalSpace.Opens.mem_iSup.mp hxtop
        obtain ⟨f, hfU, hηf⟩ :=
          W.2.exists_basicOpen_le (⟨hC.isIrreducible.genericPoint, hηU⟩ : ↥U) hηW
        have hηf' : hC.isIrreducible.genericPoint ∈ X.basicOpen f := hηf
        have hVaff : IsAffineOpen (X.basicOpen f) := W.2.basicOpen f
        exact not_mem_support_of_stalkIdeal_eq_maximalIdeal p hVaff (c.restrict hfU) hts
          (restrictIdeal_eq_restrict_coordIdeal_of_le hfU c D {t} hDU)
          (restrictIdeal_eq_restrict_coordIdeal_of_le hfU c E[j] {s} (hsome j hj s haj))
          hηf' hmaxD hmem'
  have hprod : (E.map (fun D' => stalkIdeal (monomialPartAlongDivisor I D') hC.isIrreducible.genericPoint)).prod
      = stalkIdeal (monomialPartAlongDivisor I E[i0]) hC.isIrreducible.genericPoint := by
    refine prod_map_eq_apply_getElem_of_forall_ne
      (fun D' => stalkIdeal (monomialPartAlongDivisor I D') hC.isIrreducible.genericPoint) E i0 hi0 ?_
    intro j hj hji0
    show stalkIdeal (monomialPartAlongDivisor I E[j]) hC.isIrreducible.genericPoint = 1
    have h1 : stalkIdeal (monomialPartAlongDivisor I E[j]) hC.isIrreducible.genericPoint = ⊤ :=
      stalkIdeal_monomialPartAlongDivisor_of_not_mem_support I E[j] (hother j hj hji0)
    rw [h1, Ideal.one_eq_top]
  rw [stalkIdeal_monomialFactorIdeal, hprod, hi0D,
    stalkIdeal_monomialPartAlongDivisor_of_mem p I hloc hC hC.genericPoint_mem]
private theorem exists_affineOpens_ideal_comap_ι_eq_map (Ω : X.Opens)
    (V : Ω.toScheme.affineOpens) :
    ∃ (W : X.affineOpens) (e : (V : Ω.toScheme.Opens) ≤
        (TopologicalSpace.Opens.map Ω.ι.base).obj (W : X.Opens)),
      (W : X.Opens) ≤ Ω ∧ ∀ A : X.IdealSheafData,
        (A.comap Ω.ι).ideal V
          = Ideal.map (Ω.ι.appLE (W : X.Opens) (V : Ω.toScheme.Opens) e).hom (A.ideal W) := by
  have haff : IsAffineOpen (Ω.ι ''ᵁ (V : Ω.toScheme.Opens)) :=
    V.2.image_of_isOpenImmersion Ω.ι
  have he : (V : Ω.toScheme.Opens) ≤
      (TopologicalSpace.Opens.map Ω.ι.base).obj (Ω.ι ''ᵁ (V : Ω.toScheme.Opens)) := by
    intro y hy
    exact ⟨y, hy, rfl⟩
  have hle : (Ω.ι ''ᵁ (V : Ω.toScheme.Opens)) ≤ Ω := by
    rintro z ⟨y, -, rfl⟩
    exact y.2
  exact ⟨⟨_, haff⟩, he, hle, fun A =>
    Scheme.IdealSheafData.comap_ideal_eq_map_appLE A Ω.ι ⟨_, haff⟩ V he⟩
private theorem comap_ι_eq_of_forall_affineOpens_ideal_eq (A B : X.IdealSheafData) (Ω : X.Opens)
    (h : ∀ W : X.affineOpens, (W : X.Opens) ≤ Ω → A.ideal W = B.ideal W) :
    A.comap Ω.ι = B.comap Ω.ι := by
  refine le_antisymm ?_ ?_
  · intro V
    obtain ⟨W, e, hW, hform⟩ := exists_affineOpens_ideal_comap_ι_eq_map Ω V
    rw [hform A, hform B, h W hW]
  · intro V
    obtain ⟨W, e, hW, hform⟩ := exists_affineOpens_ideal_comap_ι_eq_map Ω V
    rw [hform A, hform B, h W hW]
private theorem idealSheafData_comap_one (Ω : X.Opens) :
    (1 : X.IdealSheafData).comap Ω.ι = 1 := by
  rw [Scheme.IdealSheafData.one_eq_top]
  exact Scheme.IdealSheafData.comap_top _
private theorem idealSheafData_comap_prod (Ω : X.Opens) :
    ∀ (n : ℕ) (J : Fin n → X.IdealSheafData),
      (∏ i, J i).comap Ω.ι = ∏ i, (J i).comap Ω.ι := by
  intro n
  induction n with
  | zero =>
      intro J
      simp only [Finset.univ_eq_empty, Finset.prod_empty]
      exact idealSheafData_comap_one Ω
  | succ n ih =>
      intro J
      rw [Fin.prod_univ_succ, Scheme.IdealSheafData.comap_mul, ih (fun i => J i.succ),
        Fin.prod_univ_succ]
private theorem exists_nhds_ideal_monomialPartAlongDivisor_eq_pow [TopologicalSpace.NoetherianSpace ↥X]
    (p : X ⟶ Spec (CommRingCat.of k)) (I D : X.IdealSheafData)
    (hD : IsEtaleLocallyCoordinateDivisor p D) (x : X) :
    ∃ Ω : X.Opens, x ∈ Ω ∧ ∃ a : ℕ, ∀ W : X.affineOpens, (W : X.Opens) ≤ Ω →
      (monomialPartAlongDivisor I D).ideal W = (D ^ a).ideal W := by
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
    refine ⟨V, hxV, orderAlongComponent I hC₀.isIrreducible, ?_⟩
    intro W hWV
    have hres : restrictIdeal D (W : X.Opens) = (c.restrict hWV).coordIdeal {j} :=
      restrictIdeal_eq_restrict_coordIdeal_of_le hWV c D {j} hDV
    have hDW : D.ideal W = Ideal.span {(c.restrict hWV).coord j} := by
      have h1 := EtaleChart.ideal_eq_span_coord (c.restrict hWV) W.2 D {j} hres
      simpa using h1
    have hcomp0 : (componentPowerIdeal I D C₀).ideal W
        = Ideal.span {(c.restrict hWV).coord j ^ orderAlongComponent I hC₀.isIrreducible} := by
      rw [componentPowerIdeal_of_isIrreducibleComponentOfSupport I D hC₀, idealSheafData_ideal_pow,
        hagree W hWV, hDW, Ideal.span_singleton_pow]
    have hDpow : (D ^ orderAlongComponent I hC₀.isIrreducible).ideal W
        = Ideal.span {(c.restrict hWV).coord j ^ orderAlongComponent I hC₀.isIrreducible} := by
      rw [idealSheafData_ideal_pow, hDW, Ideal.span_singleton_pow]
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
    rw [hDpow, ← hcomp0]
    refine le_antisymm ?_ ?_
    · have hle : monomialPartAlongDivisor I D ≤ componentPowerIdeal I D C₀ := by
        rw [monomialPartAlongDivisor_eq_inf_componentPowerIdeal]
        exact Finset.inf_le hC₀mem
      exact hle W
    · rw [← hprodideal]
      exact hprodle W
  · push Not at hx
    have hclosed : IsClosed (⋃ C ∈ (supportComponentsFinset D : Set (Set X)), C) := by
      refine Set.Finite.isClosed_biUnion (supportComponentsFinset D).finite_toSet ?_
      intro C hC
      exact ((hmemiff C).mp (Finset.mem_coe.mp hC)).isClosed
    refine ⟨⟨(⋃ C ∈ (supportComponentsFinset D : Set (Set X)), C)ᶜ, hclosed.isOpen_compl⟩,
      ?_, 0, ?_⟩
    · intro hmem
      rw [Set.mem_iUnion₂] at hmem
      obtain ⟨C, hC, hxC⟩ := hmem
      exact hx C (Finset.mem_coe.mp hC) hxC
    · intro W hWΩ
      rw [pow_zero, idealSheafData_ideal_one, Ideal.one_eq_top]
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
private theorem exists_prod_monomialPartAlongDivisor_eq_prod_pow
    [TopologicalSpace.NoetherianSpace ↥X] (p : X ⟶ Spec (CommRingCat.of k))
    (I : X.IdealSheafData) (x : X) :
    ∀ (n : ℕ) (g : Fin n → X.IdealSheafData), (∀ i, IsEtaleLocallyCoordinateDivisor p (g i)) →
      ∃ Ω : X.Opens, x ∈ Ω ∧ ∃ a : Fin n → ℕ, ∀ W : X.affineOpens, (W : X.Opens) ≤ Ω →
        ((List.ofFn fun i => monomialPartAlongDivisor I (g i)).prod).ideal W = (∏ i, g i ^ a i).ideal W := by
  intro n
  induction n with
  | zero =>
      intro g _
      refine ⟨⊤, trivial, Fin.elim0, ?_⟩
      intro W _
      simp only [List.ofFn_zero, List.prod_nil, Finset.univ_eq_empty, Finset.prod_empty]
  | succ n ih =>
      intro g hg
      obtain ⟨Ω₁, hxΩ₁, a₀, h₁⟩ := exists_nhds_ideal_monomialPartAlongDivisor_eq_pow p I (g 0) (hg 0) x
      obtain ⟨Ω₂, hxΩ₂, a', h₂⟩ := ih (fun i => g i.succ) (fun i => hg i.succ)
      refine ⟨Ω₁ ⊓ Ω₂, ⟨hxΩ₁, hxΩ₂⟩, Fin.cons a₀ a', ?_⟩
      intro W hW
      have e1 := h₁ W (le_trans hW inf_le_left)
      have e2 := h₂ W (le_trans hW inf_le_right)
      simp only [List.ofFn_succ, List.prod_cons, Fin.prod_univ_succ]
      rw [idealSheafData_ideal_mul, idealSheafData_ideal_mul, e1, e2]
      simp only [Fin.cons_zero, Fin.cons_succ]
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
theorem _root_.solution [TopologicalSpace.NoetherianSpace ↥X] [IsLocallyNoetherian X]
    [CharZero k] (p : X ⟶ Spec (CommRingCat.of k)) [AlgebraicGeometry.Smooth p]
    [LocallyOfFiniteType p] [QuasiCompact p] (E : List X.IdealSheafData)
    (hE : InStrictNormalCrossingPosition p E) (I : X.IdealSheafData) (hI : NonzeroOnComponents I) :
    ∃ M N : X.IdealSheafData, IsMonomialSplitting E I M N := by
  classical
  have hetaleCoord : ∀ i : Fin E.length, IsEtaleLocallyCoordinateDivisor p (E.get i) := by
    intro i
    refine isEtaleLocallyCoordinateDivisor_of_inStrictNormalCrossingPosition p E hE _ ?_
    simp
  refine ⟨monomialFactorIdeal E I, nonMonomialFactorIdeal E I, ?_, ?_, ?_, ?_⟩
  · exact (monomialFactorIdeal_mul_nonMonomialFactorIdeal p E I hE).symm
  · intro z hz
    by_contra hcon
    have hnot : ∀ D ∈ E, z ∉ (D.support : Set X) := by
      intro D hD hmem
      refine hcon ?_
      rw [Set.mem_iUnion₂]
      exact ⟨D, hD, hmem⟩
    have htop : stalkIdeal (monomialFactorIdeal E I) z = ⊤ := by
      rw [stalkIdeal_monomialFactorIdeal, ← Ideal.one_eq_top]
      refine prod_map_eq_one_of_forall_eq_one (fun D => stalkIdeal (monomialPartAlongDivisor I D) z) E ?_
      intro D hD
      rw [stalkIdeal_monomialPartAlongDivisor_of_not_mem_support I D (hnot D hD), Ideal.one_eq_top]
    have hz' : z ∈ (monomialFactorIdeal E I).support := hz
    exact (mem_support_iff_stalkIdeal_ne_top (monomialFactorIdeal E I) z).mp hz' htop
  · intro x
    obtain ⟨Ω, hxΩ, a, ha⟩ :=
      exists_prod_monomialPartAlongDivisor_eq_prod_pow p I x E.length E.get hetaleCoord
    refine ⟨Ω, hxΩ, a, ?_⟩
    have hlist : (List.ofFn fun i : Fin E.length => monomialPartAlongDivisor I (E.get i))
        = E.map fun D => monomialPartAlongDivisor I D := by
      refine List.ext_getElem (by simp) ?_
      intro i h1 h2
      simp
    have hcongr : (monomialFactorIdeal E I).comap Ω.ι
        = (∏ i : Fin E.length, E.get i ^ a i).comap Ω.ι := by
      refine comap_ι_eq_of_forall_affineOpens_ideal_eq _ _ Ω ?_
      intro W hW
      have hW' := ha W hW
      rw [hlist] at hW'
      rw [monomialFactorIdeal_eq_prod_monomialPartAlongDivisor]
      exact hW'
    rw [hcongr, idealSheafData_comap_prod Ω E.length (fun i => E.get i ^ a i)]
    exact Finset.prod_congr rfl
      (fun i _ => Scheme.IdealSheafData.comap_pow (E.get i) Ω.ι (a i))
  · intro D hD C hCirr hCsub hCmax hCN
    have hC : IsIrreducibleComponentOfSupport D C :=
      { isIrreducible := hCirr
        maximal := fun C' h1 h2 h3 => Set.Subset.antisymm (hCmax C' h1 h3 h2) h2
        subset_support := hCsub }
    have hloc : IsEtaleLocallyCoordinateDivisor p D := isEtaleLocallyCoordinateDivisor_of_inStrictNormalCrossingPosition p E hE D hD
    have hmaxD : stalkIdeal D hC.isIrreducible.genericPoint
        = IsLocalRing.maximalIdeal (X.presheaf.stalk hC.isIrreducible.genericPoint) :=
      stalkIdeal_genericPoint_eq_maximalIdeal p D hloc hC.isIrreducible hC.subset_support
        hC.maximal
    have hstalkM : stalkIdeal (monomialFactorIdeal E I) hC.isIrreducible.genericPoint
        = IsLocalRing.maximalIdeal (X.presheaf.stalk hC.isIrreducible.genericPoint)
          ^ orderAlongComponent I hC.isIrreducible := by
      rw [stalkIdeal_monomialFactorIdeal_genericPoint p E I hE hD hC, hmaxD]
    have hN : stalkIdeal (nonMonomialFactorIdeal E I) hC.isIrreducible.genericPoint
        ≤ IsLocalRing.maximalIdeal (X.presheaf.stalk hC.isIrreducible.genericPoint) :=
      (mem_support_iff_stalkIdeal_le_maximalIdeal _ _).mp (hCN hC.genericPoint_mem)
    have hIeq : stalkIdeal I hC.isIrreducible.genericPoint
        = stalkIdeal (monomialFactorIdeal E I) hC.isIrreducible.genericPoint
          * stalkIdeal (nonMonomialFactorIdeal E I) hC.isIrreducible.genericPoint := by
      rw [← stalkIdeal_mul, monomialFactorIdeal_mul_nonMonomialFactorIdeal p E I hE]
    have hle : stalkIdeal I hC.isIrreducible.genericPoint
        ≤ IsLocalRing.maximalIdeal (X.presheaf.stalk hC.isIrreducible.genericPoint)
          ^ (orderAlongComponent I hC.isIrreducible + 1) := by
      rw [hIeq, hstalkM, pow_succ]
      exact Ideal.mul_mono le_rfl hN
    have h2 : ((orderAlongComponent I hC.isIrreducible + 1 : ℕ) : ℕ∞)
        ≤ orderAt I hC.isIrreducible.genericPoint :=
      (le_orderAt_iff I _ _).mpr hle
    rw [← coe_orderAlongComponent_eq_orderAt_genericPoint hC hI] at h2
    have h3 : orderAlongComponent I hC.isIrreducible + 1
        ≤ orderAlongComponent I hC.isIrreducible := by exact_mod_cast h2
    omega
end FunctorialResolution.EmbeddedResolution
