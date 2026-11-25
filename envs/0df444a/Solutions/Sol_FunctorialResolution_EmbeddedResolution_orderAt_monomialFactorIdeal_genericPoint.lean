-- Prove2me | solution 1 for FunctorialResolution.EmbeddedResolution.orderAt_monomialFactorIdeal_genericPoint
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T02:39:42.743816+00:00
-- url     : https://prove2.me/submissions/30a297ad-082e-4d48-a534-acc66f3c2ae3

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
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_stalkIdeal_monomialPartAlongDivisor_of_not_mem_support
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_stalkIdeal_monomialPartAlongDivisor_of_mem
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_stalkIdeal_monomialFactorIdeal
import Theorems.Thm_Derivation_liftToLocalization_algebraMap
import Theorems.Thm_Derivation_mapToLocalization_algebraMap
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_EtaleChart_coordRingHom_X
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_EtaleChart_ofCoords_map
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_EtaleCoordinates_basisDerivation_apply
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_HasStrictNormalCrossingsWith_exists_etaleChart
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_InStrictNormalCrossingPositionAt_exists_etaleChart
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
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_le_orderAt_iff
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_mem_span_coord_of_coord_mul_mem
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_mem_support_iff_stalkIdeal_le_maximalIdeal
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_notMem_support_of_mem_opens_of_restrictIdeal_eq_top
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_not_stalkIdeal_le_pow_succ_genericPoint
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_pullbackCoord_def
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_restrictIdeal_eq_restrict_coordIdeal_of_le
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_stalkIdeal_eq_span_germ_coord
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_stalkIdeal_genericPoint_eq_maximalIdeal
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_stalkIdeal_le_pow_of_le_orderAt_genericPoint
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
private theorem prod_map_eq_one_of_forall_eq_one {α : Type*} {M : Type*} [CommMonoid M]
    (g : α → M) (L : List α) (h : ∀ b ∈ L, g b = 1) : (L.map g).prod = 1 :=
  List.prod_eq_one fun x hx => by
    obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hx
    exact h a ha
private theorem natCast_add_one_le_of_not_le (n : ℕ) (b : ℕ∞) (h : ¬ b ≤ (n : ℕ∞)) :
    ((n + 1 : ℕ) : ℕ∞) ≤ b := by
  rw [Nat.cast_succ]
  exact ENat.natCast_add_one_le_iff.2 (not_le.mp h)
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
    [IsLocallyNoetherian X] (p : X ⟶ Spec (CommRingCat.of k)) [LocallyOfFiniteType p]
    (E : List X.IdealSheafData) (I : X.IdealSheafData) (hE : InStrictNormalCrossingPosition p E)
    (hI : NonzeroOnComponents I) {D : X.IdealSheafData} (hD : D ∈ E) {C : Set X}
    (hC : IsIrreducibleComponentOfSupport D C) :
    orderAt (monomialFactorIdeal E I) hC.isIrreducible.genericPoint =
      (orderAlongComponent I hC.isIrreducible : ℕ∞) := by
  classical
  have hloc : IsEtaleLocallyCoordinateDivisor p D := isEtaleLocallyCoordinateDivisor_of_inStrictNormalCrossingPosition p E hE D hD
  have hmaxD : stalkIdeal D hC.isIrreducible.genericPoint
      = IsLocalRing.maximalIdeal (X.presheaf.stalk hC.isIrreducible.genericPoint) :=
    stalkIdeal_genericPoint_eq_maximalIdeal p D hloc hC.isIrreducible hC.subset_support hC.maximal
  have hstalk : stalkIdeal (monomialFactorIdeal E I) hC.isIrreducible.genericPoint
      = stalkIdeal D hC.isIrreducible.genericPoint ^ orderAlongComponent I hC.isIrreducible :=
    stalkIdeal_monomialFactorIdeal_genericPoint p E I hE hD hC
  have hmono : stalkIdeal (monomialFactorIdeal E I) hC.isIrreducible.genericPoint
      = IsLocalRing.maximalIdeal (X.presheaf.stalk hC.isIrreducible.genericPoint)
        ^ orderAlongComponent I hC.isIrreducible := by
    rw [hstalk, hmaxD]
  have hordI : orderAt I hC.isIrreducible.genericPoint
      = ((orderAlongComponent I hC.isIrreducible : ℕ) : ℕ∞) :=
    (coe_orderAlongComponent_eq_orderAt_genericPoint hC hI).symm
  have h3 : stalkIdeal I hC.isIrreducible.genericPoint
      ≤ IsLocalRing.maximalIdeal (X.presheaf.stalk hC.isIrreducible.genericPoint)
        ^ orderAlongComponent I hC.isIrreducible := by
    rw [← hmaxD]
    exact stalkIdeal_le_pow_of_le_orderAt_genericPoint p D hloc hC.isIrreducible
      hC.subset_support hC.maximal I (orderAlongComponent I hC.isIrreducible)
      (le_of_eq hordI.symm) hC.isIrreducible.genericPoint hC.genericPoint_mem
  refine le_antisymm ?_ ((le_orderAt_iff _ _ _).mpr (le_of_eq hmono))
  by_contra hcon
  have h2 : ((orderAlongComponent I hC.isIrreducible + 1 : ℕ) : ℕ∞)
      ≤ orderAt (monomialFactorIdeal E I) hC.isIrreducible.genericPoint :=
    natCast_add_one_le_of_not_le (orderAlongComponent I hC.isIrreducible) _ hcon
  rw [le_orderAt_iff, hmono] at h2
  exact not_stalkIdeal_le_pow_succ_genericPoint p D hloc hC.isIrreducible hC.subset_support
    hC.maximal I (orderAlongComponent I hC.isIrreducible) hordI
    (by rw [hmaxD]; exact le_trans h3 h2)
end FunctorialResolution.EmbeddedResolution
