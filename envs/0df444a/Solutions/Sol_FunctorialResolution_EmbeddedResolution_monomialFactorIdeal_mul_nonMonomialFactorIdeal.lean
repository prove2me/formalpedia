-- Prove2me | solution 1 for FunctorialResolution.EmbeddedResolution.monomialFactorIdeal_mul_nonMonomialFactorIdeal
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T02:39:41.470365+00:00
-- url     : https://prove2.me/submissions/ff435d74-a160-4d01-9d06-1f4fa80e368b

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
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_orderAlongComponent_eq_orderAt_genericPoint
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_stalkIdeal_monomialPartAlongDivisor_of_not_mem_support
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_stalkIdeal_monomialPartAlongDivisor_of_mem
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_stalkIdeal_monomialFactorIdeal
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_isLocallyGeneratedByNonZeroDivisor_monomialFactorIdeal
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_nonMonomialFactorIdeal_eq_idealSheafColon
import Theorems.Thm_Derivation_liftToLocalization_algebraMap
import Theorems.Thm_Derivation_mapToLocalization_algebraMap
import Theorems.Thm_FunctorialResolution_Blowup_IsLocallyGeneratedByNonZeroDivisor_mul_idealSheafColon
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_EtaleChart_coordRingHom_X
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_EtaleChart_ofCoords_map
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_EtaleCoordinates_basisDerivation_apply
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_HasStrictNormalCrossingsWith_exists_etaleChart
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_InStrictNormalCrossingPositionAt_exists_etaleChart
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_coordVectorInl_inl
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_coordVectorInl_inr
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_coordVectorInr_inl
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_coordVectorInr_inr
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_derivIdealSheafIterate_ideal
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_derivIdealSheafIterate_zero
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_derivIdealSheaf_ideal
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_exists_etaleChart
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_exists_isIrreducibleComponentOfSupport
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_idealSheafColon_ideal
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_inStrictNormalCrossingPosition_iff
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_le_iff_forall_stalkIdeal_le
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_mem_span_coord_pow_of_mul_mem
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_notMem_support_of_mem_opens_of_restrictIdeal_eq_top
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_pullbackCoord_def
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_restrictIdeal_eq_restrict_coordIdeal_of_le
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_stalkIdeal_eq_span_germ_coord
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
private theorem mem_span_of_pow_mul_mem_span {R : Type*} [CommRing R] (g h : R)
    (hcan : ∀ (n : ℕ) (z : R), h * z ∈ Ideal.span ({g ^ n} : Set R) →
      z ∈ Ideal.span ({g ^ n} : Set R)) (n m : ℕ) :
    ∀ z : R, h ^ m * z ∈ Ideal.span ({g ^ n} : Set R) → z ∈ Ideal.span ({g ^ n} : Set R) := by
  induction m with
  | zero =>
      intro z hz
      simpa using hz
  | succ m ih =>
      intro z hz
      refine ih z (hcan n (h ^ m * z) ?_)
      have hmul : h * (h ^ m * z) = h ^ (m + 1) * z := by ring
      rw [hmul]
      exact hz
variable {X : Scheme.{u}}
variable {k : Type u} [Field k]
private theorem mem_prod_map_of_forall_mem_span {R : Type*} [CommRing R] {α : Type*}
    (F : α → Ideal R) :
    ∀ (L : List α) (g : ℕ → R),
      (∀ (i : ℕ) (h : i < L.length), F L[i] = Ideal.span ({g i} : Set R)) →
      (∀ (i : ℕ), i < L.length → ∀ (j : ℕ), j < L.length → i ≠ j →
        ∀ (n : ℕ) (w : R), g j * w ∈ Ideal.span ({g i ^ n} : Set R) →
          w ∈ Ideal.span ({g i ^ n} : Set R)) →
      ∀ z : R, (∀ (i : ℕ), i < L.length → z ∈ Ideal.span ({g i} : Set R)) →
        z ∈ (L.map F).prod := by
  intro L
  induction L with
  | nil =>
      intro g _ _ z _
      rw [List.map_nil, List.prod_nil, Ideal.one_eq_top]
      exact Submodule.mem_top
  | cons b L ih =>
      intro g hF hcan z hz
      have hb0 : F b = Ideal.span ({g 0} : Set R) := by
        have h := hF 0 (by simp only [List.length_cons]; omega)
        simpa using h
      have hz0 : z ∈ Ideal.span ({g 0} : Set R) :=
        hz 0 (by simp only [List.length_cons]; omega)
      obtain ⟨y, hy⟩ := Ideal.mem_span_singleton'.mp hz0
      have hzy : z = g 0 * y := by rw [← hy]; ring
      have hyprod : y ∈ (L.map F).prod := by
        refine ih (fun i => g (i + 1)) ?_ ?_ y ?_
        · intro i h
          have h2 := hF (i + 1) (by simp only [List.length_cons]; omega)
          simpa using h2
        · intro i hi j hj hij n w hw
          exact hcan (i + 1) (by simp only [List.length_cons]; omega) (j + 1)
            (by simp only [List.length_cons]; omega) (by omega) n w hw
        · intro i h
          have hzi : z ∈ Ideal.span ({g (i + 1)} : Set R) :=
            hz (i + 1) (by simp only [List.length_cons]; omega)
          have hzi' : g 0 * y ∈ Ideal.span ({g (i + 1) ^ 1} : Set R) := by
            rw [pow_one, ← hzy]
            exact hzi
          have h3 := hcan (i + 1) (by simp only [List.length_cons]; omega) 0
            (by simp only [List.length_cons]; omega) (by omega) 1 y hzi'
          rwa [pow_one] at h3
      have hg0 : g 0 ∈ F b := by
        rw [hb0]
        exact Ideal.mem_span_singleton_self _
      rw [List.map_cons, List.prod_cons, hzy]
      exact Ideal.mul_mem_mul hg0 hyprod
private theorem mem_span_algebraMap_of_mul_mem {S : Type*} [CommRing S] {q : Submonoid S}
    {A : Type*} [CommRing A] [Algebra S A] [IsLocalization q A] (b d : S)
    (hcan : ∀ w : S, b * w ∈ Ideal.span ({d} : Set S) → w ∈ Ideal.span ({d} : Set S))
    (z : A) (hz : algebraMap S A b * z ∈ Ideal.span ({algebraMap S A d} : Set A)) :
    z ∈ Ideal.span ({algebraMap S A d} : Set A) := by
  obtain ⟨u, hu⟩ := Ideal.mem_span_singleton'.mp hz
  obtain ⟨⟨z₀, w₁⟩, hz₁⟩ := IsLocalization.surj (M := q) (S := A) z
  obtain ⟨⟨u₀, w₂⟩, hu₁⟩ := IsLocalization.surj (M := q) (S := A) u
  have key : algebraMap S A (b * z₀ * (w₂ : S)) = algebraMap S A (d * u₀ * (w₁ : S)) := by
    simp only [map_mul]
    linear_combination (-(algebraMap S A b) * algebraMap S A (w₂ : S)) * hz₁ +
      (algebraMap S A d * algebraMap S A (w₁ : S)) * hu₁ +
      (-(algebraMap S A (w₁ : S)) * algebraMap S A (w₂ : S)) * hu
  obtain ⟨cc, hcc⟩ := (IsLocalization.eq_iff_exists (M := q) (S := A)).mp key
  have hmem : b * (z₀ * (w₂ : S) * (cc : S)) ∈ Ideal.span ({d} : Set S) :=
    Ideal.mem_span_singleton'.mpr ⟨u₀ * (w₁ : S) * (cc : S), by linear_combination -hcc⟩
  obtain ⟨v, hv⟩ := Ideal.mem_span_singleton'.mp (hcan _ hmem)
  have hstep : z * algebraMap S A ((w₁ : S) * (w₂ : S) * (cc : S)) ∈
      Ideal.span ({algebraMap S A d} : Set A) := by
    refine Ideal.mem_span_singleton'.mpr ⟨algebraMap S A v, ?_⟩
    have h6 : algebraMap S A (z₀ * (w₂ : S) * (cc : S)) = algebraMap S A (v * d) := by rw [hv]
    simp only [map_mul] at h6 ⊢
    linear_combination -h6 - (algebraMap S A (w₂ : S) * algebraMap S A (cc : S)) * hz₁
  have hunit : IsUnit (algebraMap S A ((w₁ : S) * (w₂ : S) * (cc : S))) := by
    have h1 := IsLocalization.map_units (M := q) (S := A) w₁
    have h2 := IsLocalization.map_units (M := q) (S := A) w₂
    have h3 := IsLocalization.map_units (M := q) (S := A) cc
    rw [map_mul, map_mul]
    exact (h1.mul h2).mul h3
  obtain ⟨eu, heu⟩ := hunit
  have h7 := (Ideal.span ({algebraMap S A d} : Set A)).mul_mem_right ((eu⁻¹ : Aˣ) : A) hstep
  rw [mul_assoc, ← heu, Units.mul_inv, mul_one] at h7
  exact h7
private theorem mem_span_germ_coord_pow_of_mul_mem (p : X ⟶ Spec (CommRingCat.of k))
    {V : X.Opens} (hV : IsAffineOpen V) {m : ℕ} (c : EtaleChart p V m) {x : X} (hx : x ∈ V)
    {i j : Fin m} (hij : i ≠ j) (N : ℕ) (z : X.presheaf.stalk x)
    (hz : (X.presheaf.germ V x hx).hom (c.coord j) * z ∈
      Ideal.span ({(X.presheaf.germ V x hx).hom (c.coord i) ^ N} : Set (X.presheaf.stalk x))) :
    z ∈ Ideal.span ({(X.presheaf.germ V x hx).hom (c.coord i) ^ N} :
      Set (X.presheaf.stalk x)) := by
  let : Algebra Γ(X, V) (X.presheaf.stalk x) := (X.presheaf.germ V x hx).hom.toAlgebra
  have : IsLocalization (hV.primeIdealOf ⟨x, hx⟩).asIdeal.primeCompl (X.presheaf.stalk x) :=
    hV.isLocalization_stalk ⟨x, hx⟩
  have hmap : ∀ y : Γ(X, V), algebraMap Γ(X, V) (X.presheaf.stalk x) y =
      (X.presheaf.germ V x hx).hom y := fun _ => rfl
  have hpow : algebraMap Γ(X, V) (X.presheaf.stalk x) (c.coord i ^ N) =
      (X.presheaf.germ V x hx).hom (c.coord i) ^ N := by
    rw [map_pow, hmap]
  have hmain := mem_span_algebraMap_of_mul_mem
    (q := (hV.primeIdealOf ⟨x, hx⟩).asIdeal.primeCompl) (c.coord j) (c.coord i ^ N)
    (fun w hw => mem_span_coord_pow_of_mul_mem hV c hij N w hw) z
    (by rw [hpow, hmap]; exact hz)
  rwa [hpow] at hmain
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
    (E : List X.IdealSheafData) (I : X.IdealSheafData) (hE : InStrictNormalCrossingPosition p E) :
    monomialFactorIdeal E I * nonMonomialFactorIdeal E I = I := by
  have hM : Blowup.IsLocallyGeneratedByNonZeroDivisor (monomialFactorIdeal E I) :=
    isLocallyGeneratedByNonZeroDivisor_monomialFactorIdeal p E I hE
  have hIM : I ≤ monomialFactorIdeal E I := by
    rw [le_iff_forall_stalkIdeal_le]
    intro x
    obtain ⟨-, hposall⟩ := (inStrictNormalCrossingPosition_iff p E).mp hE
    obtain ⟨U, hxU, m, c, aa, hinj, hnone, hsome⟩ := InStrictNormalCrossingPositionAt.exists_etaleChart (hposall x)
    obtain ⟨V, hVaff, hxV, hVU⟩ := exists_isAffineOpen_mem_and_subset hxU
    have hdata : ∀ i : ℕ, ∃ ee : X.presheaf.stalk x, ∀ h : i < E.length,
        stalkIdeal (monomialPartAlongDivisor I (E[i]'h)) x = Ideal.span ({ee} : Set (X.presheaf.stalk x)) ∧
        stalkIdeal I x ≤ Ideal.span ({ee} : Set (X.presheaf.stalk x)) ∧
        (ee = 1 ∨ ∃ (t : Fin m) (bb : ℕ), aa i = some t ∧
          ee = (X.presheaf.germ V x hxV).hom ((c.restrict hVU).coord t) ^ bb) := by
      intro i
      by_cases hi : i < E.length
      · by_cases hxs : x ∈ (((E[i]'hi)).support : Set ↥X)
        · have hDloc : IsEtaleLocallyCoordinateDivisor p (E[i]'hi) :=
            isEtaleLocallyCoordinateDivisor_of_inStrictNormalCrossingPosition p E hE (E[i]'hi) (List.getElem_mem hi)
          obtain ⟨C, hC, hxC⟩ := exists_isIrreducibleComponentOfSupport (E[i]'hi) x hxs
          have hopt : ∃ t : Fin m, aa i = some t := by
            by_contra hcon
            push Not at hcon
            have hnone' : aa i = none := by
              cases hca : aa i with
              | none => rfl
              | some t => exact absurd hca (hcon t)
            exact absurd hxs (notMem_support_of_mem_opens_of_restrictIdeal_eq_top (E[i]'hi) U
              (hnone i hi hnone') x hxU)
          obtain ⟨t, haa⟩ := hopt
          have hDU : restrictIdeal (E[i]'hi) U = c.coordIdeal {t} := hsome i hi t haa
          have hDV : restrictIdeal (E[i]'hi) V = (c.restrict hVU).coordIdeal {t} :=
            restrictIdeal_eq_restrict_coordIdeal_of_le hVU c (E[i]'hi) {t} hDU
          have hst : stalkIdeal (E[i]'hi) x =
              Ideal.span ({(X.presheaf.germ V x hxV).hom ((c.restrict hVU).coord t)} :
                Set (X.presheaf.stalk x)) :=
            stalkIdeal_eq_span_germ_coord p hVaff (c.restrict hVU) t (E[i]'hi) hDV x hxV
          have hA : stalkIdeal (monomialPartAlongDivisor I (E[i]'hi)) x =
              Ideal.span ({(X.presheaf.germ V x hxV).hom ((c.restrict hVU).coord t) ^
                orderAlongComponent I hC.isIrreducible} : Set (X.presheaf.stalk x)) := by
            rw [stalkIdeal_monomialPartAlongDivisor_of_mem p I hDloc hC hxC, hst, Ideal.span_singleton_pow]
          have hB : stalkIdeal I x ≤
              Ideal.span ({(X.presheaf.germ V x hxV).hom ((c.restrict hVU).coord t) ^
                orderAlongComponent I hC.isIrreducible} : Set (X.presheaf.stalk x)) := by
            have hn : ((orderAlongComponent I hC.isIrreducible : ℕ) : ℕ∞) ≤
                orderAt I hC.isIrreducible.genericPoint := by
              rw [orderAlongComponent_eq_orderAt_genericPoint]
              exact ENat.natCast_toNat_le_self _
            have hle := stalkIdeal_le_pow_of_le_orderAt_genericPoint p (E[i]'hi) hDloc
              hC.isIrreducible hC.subset_support hC.maximal I
              (orderAlongComponent I hC.isIrreducible) hn x hxC
            rwa [hst, Ideal.span_singleton_pow] at hle
          exact ⟨(X.presheaf.germ V x hxV).hom ((c.restrict hVU).coord t) ^
            orderAlongComponent I hC.isIrreducible,
            fun _ => ⟨hA, hB, Or.inr ⟨t, orderAlongComponent I hC.isIrreducible, haa, rfl⟩⟩⟩
        · have hA : stalkIdeal (monomialPartAlongDivisor I (E[i]'hi)) x =
              Ideal.span ({1} : Set (X.presheaf.stalk x)) := by
            rw [stalkIdeal_monomialPartAlongDivisor_of_not_mem_support I (E[i]'hi) hxs,
              Ideal.span_singleton_one]
          have hB : stalkIdeal I x ≤ Ideal.span ({1} : Set (X.presheaf.stalk x)) := by
            rw [Ideal.span_singleton_one]
            exact le_top
          exact ⟨1, fun _ => ⟨hA, hB, Or.inl rfl⟩⟩
      · exact ⟨1, fun h => absurd h hi⟩
    choose ee hee using hdata
    have hcan : ∀ (i : ℕ), i < E.length → ∀ (j : ℕ), j < E.length → i ≠ j →
        ∀ (n : ℕ) (w : X.presheaf.stalk x),
          ee j * w ∈ Ideal.span ({ee i ^ n} : Set (X.presheaf.stalk x)) →
            w ∈ Ideal.span ({ee i ^ n} : Set (X.presheaf.stalk x)) := by
      intro i hi j hj hij n w hw
      rcases (hee i hi).2.2 with hi1 | ⟨ti, bi, hai, hei⟩
      · rw [hi1, one_pow, Ideal.span_singleton_one]
        exact Submodule.mem_top
      · rcases (hee j hj).2.2 with hj1 | ⟨tj, bj, haj, hej⟩
        · rw [hj1, one_mul] at hw
          exact hw
        · have htne : ti ≠ tj := by
            intro htt
            refine hij ?_
            have haj' : aa j = some ti := by rw [htt]; exact haj
            exact hinj i hi j hj ti hai haj'
          have hsingle : ∀ (N : ℕ) (zz : X.presheaf.stalk x),
              (X.presheaf.germ V x hxV).hom ((c.restrict hVU).coord tj) * zz ∈
                Ideal.span ({(X.presheaf.germ V x hxV).hom ((c.restrict hVU).coord ti) ^ N} :
                  Set (X.presheaf.stalk x)) →
              zz ∈ Ideal.span ({(X.presheaf.germ V x hxV).hom ((c.restrict hVU).coord ti) ^ N} :
                  Set (X.presheaf.stalk x)) :=
            fun N zz hzz =>
              mem_span_germ_coord_pow_of_mul_mem p hVaff (c.restrict hVU) hxV htne N zz hzz
          rw [hei, hej] at hw
          rw [hei]
          rw [← pow_mul] at hw ⊢
          exact mem_span_of_pow_mul_mem_span _ _ hsingle (bi * n) bj w hw
    rw [stalkIdeal_monomialFactorIdeal]
    intro z hz
    refine mem_prod_map_of_forall_mem_span (fun D => stalkIdeal (monomialPartAlongDivisor I D) x) E ee ?_
      hcan z ?_
    · intro i h
      exact (hee i h).1
    · intro i h
      exact (hee i h).2.1 hz
  rw [nonMonomialFactorIdeal_eq_idealSheafColon]
  exact hM.mul_idealSheafColon hIM
end FunctorialResolution.EmbeddedResolution
