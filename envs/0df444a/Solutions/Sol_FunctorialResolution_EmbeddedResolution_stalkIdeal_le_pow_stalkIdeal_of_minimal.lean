-- Prove2me | solution 1 for FunctorialResolution.EmbeddedResolution.stalkIdeal_le_pow_stalkIdeal_of_minimal
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T01:25:09.193075+00:00
-- url     : https://prove2.me/submissions/60930a62-1125-42ac-acfa-d7eee19c066c

import Mathlib
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_EtaleCoordinates_CoordinateDivisibility
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_EtaleCoordinates_CoordinateDivisorSmoothness
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_EtaleCoordinates_CoordinatePolynomialRing
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_EtaleCoordinates_ChartRing
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_EtaleCoordinates_EtaleChartExistence
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_EtaleCoordinates_StrictNormalCrossings
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_DerivativeIdeal_IdealSheafOrder
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_DerivativeIdeal_OrderAtGenericPoint
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_stalkIdeal_eq_span_germ_coord
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_primeIdealOf_eq_comap_span_germ_coord
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_stalkIdeal_eq_maximalIdeal_of_minimal
import Theorems.Thm_Derivation_liftToLocalization_algebraMap
import Theorems.Thm_Derivation_mapToLocalization_algebraMap
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_EtaleChart_coordRingHom_X
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_EtaleChart_ofCoords_map
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_EtaleCoordinates_basisDerivation_apply
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_coordVectorInl_inl
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_coordVectorInl_inr
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_coordVectorInr_inl
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_coordVectorInr_inr
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_coord_mem_nonZeroDivisors
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_derivIdealSheafIterate_ideal
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_derivIdealSheafIterate_zero
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_derivIdealSheaf_ideal
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_germ_mem_stalkIdeal
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_le_orderAt_iff
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_pullbackCoord_def
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
attribute [local simp] FunctorialResolution.EmbeddedResolution.pullbackCoord_def


section
universe u
open CategoryTheory Opposite AlgebraicGeometry TopologicalSpace
noncomputable section
namespace FunctorialResolution.EmbeddedResolution
variable {X : Scheme.{u}} {k : Type u} [Field k] (p : X ⟶ Spec (CommRingCat.of k))
private theorem mem_span_pow_of_mul_mem_span_pow {A : Type*} [CommRing A] (τ : A)
    (hprime : (Ideal.span ({τ} : Set A)).IsPrime) (hnzd : τ ∈ nonZeroDivisors A) (a : ℕ) :
    ∀ s f : A, s ∉ Ideal.span ({τ} : Set A) →
      s * f ∈ Ideal.span ({τ ^ a} : Set A) → f ∈ Ideal.span ({τ ^ a} : Set A) := by
  induction a with
  | zero =>
      intro s f _ _
      rw [pow_zero, Ideal.span_singleton_one]
      exact Submodule.mem_top
  | succ b ih =>
      intro s f hs hsf
      obtain ⟨d, hd⟩ := Ideal.mem_span_singleton.mp hsf
      have hsf1 : s * f ∈ Ideal.span ({τ} : Set A) := by
        refine Ideal.mem_span_singleton.mpr ⟨τ ^ b * d, ?_⟩
        rw [hd]
        ring
      have hf1 : f ∈ Ideal.span ({τ} : Set A) := (hprime.mem_or_mem hsf1).resolve_left hs
      obtain ⟨f', rfl⟩ := Ideal.mem_span_singleton.mp hf1
      have hcancel : (s * f' - τ ^ b * d) * τ = 0 := by
        have h2 : (s * f' - τ ^ b * d) * τ = s * (τ * f') - τ ^ (b + 1) * d := by ring
        rw [h2, hd, sub_self]
      have hsf' : s * f' = τ ^ b * d :=
        eq_of_sub_eq_zero ((mem_nonZeroDivisors_iff.mp hnzd).2 _ hcancel)
      have hf' : f' ∈ Ideal.span ({τ ^ b} : Set A) :=
        ih s f' hs (Ideal.mem_span_singleton.mpr ⟨d, hsf'⟩)
      obtain ⟨e, he⟩ := Ideal.mem_span_singleton.mp hf'
      refine Ideal.mem_span_singleton.mpr ⟨e, ?_⟩
      rw [he]
      ring
end FunctorialResolution.EmbeddedResolution
end
end

set_option autoImplicit false
universe u
open CategoryTheory Opposite AlgebraicGeometry TopologicalSpace
noncomputable section
open FunctorialResolution FunctorialResolution.EmbeddedResolution
variable {X : Scheme.{u}} {k : Type u} [Field k] (p : X ⟶ Spec (CommRingCat.of k))
namespace FunctorialResolution.EmbeddedResolution
theorem _root_.solution {V : X.Opens} (hV : IsAffineOpen V) {n : ℕ}
    (c : EtaleChart p V n) (j : Fin n) (D : X.IdealSheafData)
    (hD : restrictIdeal D V = c.coordIdeal {j}) (x η : X) (hx : x ∈ V) (hη : η ∈ V)
    (hspec : η ⤳ x) (hηs : η ∈ D.support)
    (hmin : ∀ P : Ideal Γ(X, V), P.IsPrime → c.coord j ∈ P →
      P ≤ (hV.primeIdealOf ⟨η, hη⟩).asIdeal → P = (hV.primeIdealOf ⟨η, hη⟩).asIdeal)
    (I : X.IdealSheafData) (a : ℕ) (ha : (a : ℕ∞) ≤ orderAt I η) :
    stalkIdeal I x ≤ stalkIdeal D x ^ a := by
  let _ : Algebra (Γ(X, V)) (X.presheaf.stalk x) := (X.presheaf.germ V x hx).hom.toAlgebra
  have : IsLocalization.AtPrime (X.presheaf.stalk x) (hV.primeIdealOf ⟨x, hx⟩).asIdeal :=
    hV.isLocalization_stalk ⟨x, hx⟩
  let _ : Algebra (Γ(X, V)) (X.presheaf.stalk η) := (X.presheaf.germ V η hη).hom.toAlgebra
  have : IsLocalization.AtPrime (X.presheaf.stalk η) (hV.primeIdealOf ⟨η, hη⟩).asIdeal :=
    hV.isLocalization_stalk ⟨η, hη⟩
  have halgη : (algebraMap (Γ(X, V)) (X.presheaf.stalk η)) = (X.presheaf.germ V η hη).hom := rfl
  have hqcomap : (hV.primeIdealOf ⟨η, hη⟩).asIdeal =
      Ideal.comap (X.presheaf.germ V x hx).hom
        (Ideal.span ({(X.presheaf.germ V x hx).hom (c.coord j)} : Set (X.presheaf.stalk x))) :=
    primeIdealOf_eq_comap_span_germ_coord p hV c j D hD x η hx hη hspec hηs hmin
  have hqle : ∀ z : Γ(X, V), (X.presheaf.germ V x hx).hom z ∈
      Ideal.span ({(X.presheaf.germ V x hx).hom (c.coord j)} : Set (X.presheaf.stalk x)) →
      z ∈ (hV.primeIdealOf ⟨η, hη⟩).asIdeal := by
    intro z hz
    rw [hqcomap]
    exact hz
  have hnetop : (Ideal.span ({(X.presheaf.germ V x hx).hom (c.coord j)} :
      Set (X.presheaf.stalk x))) ≠ ⊤ := by
    intro hcon
    have h1 : (hV.primeIdealOf ⟨η, hη⟩).asIdeal = ⊤ := by
      rw [hqcomap, hcon, Ideal.comap_top]
    exact (hV.primeIdealOf ⟨η, hη⟩).isPrime.ne_top h1
  have hqp : (hV.primeIdealOf ⟨η, hη⟩).asIdeal ≤ (hV.primeIdealOf ⟨x, hx⟩).asIdeal := by
    intro r hr
    by_contra hcon
    have hunit : IsUnit ((X.presheaf.germ V x hx).hom r) :=
      IsLocalization.map_units (S := X.presheaf.stalk x)
        (M := (hV.primeIdealOf ⟨x, hx⟩).asIdeal.primeCompl) ⟨r, hcon⟩
    have hmemr : (X.presheaf.germ V x hx).hom r ∈
        Ideal.span ({(X.presheaf.germ V x hx).hom (c.coord j)} : Set (X.presheaf.stalk x)) := by
      rw [hqcomap] at hr
      exact hr
    exact hnetop (Ideal.eq_top_of_isUnit_mem _ hmemr hunit)
  have hdisj : Disjoint ((hV.primeIdealOf ⟨x, hx⟩).asIdeal.primeCompl : Set (Γ(X, V)))
      ((hV.primeIdealOf ⟨η, hη⟩).asIdeal : Set (Γ(X, V))) := by
    rw [Set.disjoint_left]
    intro r hr hr'
    have hr1 : r ∉ (hV.primeIdealOf ⟨x, hx⟩).asIdeal := hr
    exact hr1 (hqp hr')
  have hqcomap' : (hV.primeIdealOf ⟨η, hη⟩).asIdeal =
      Ideal.comap (algebraMap (Γ(X, V)) (X.presheaf.stalk x))
        (Ideal.span ({(X.presheaf.germ V x hx).hom (c.coord j)} : Set (X.presheaf.stalk x))) :=
    hqcomap
  have hmapq : Ideal.map (algebraMap (Γ(X, V)) (X.presheaf.stalk x))
      (hV.primeIdealOf ⟨η, hη⟩).asIdeal =
      Ideal.span ({(X.presheaf.germ V x hx).hom (c.coord j)} : Set (X.presheaf.stalk x)) := by
    rw [hqcomap']
    exact IsLocalization.map_under (M := (hV.primeIdealOf ⟨x, hx⟩).asIdeal.primeCompl)
      (S := X.presheaf.stalk x) _
  have hprime : (Ideal.span ({(X.presheaf.germ V x hx).hom (c.coord j)} :
      Set (X.presheaf.stalk x))).IsPrime := by
    rw [← hmapq]
    exact IsLocalization.isPrime_of_isPrime_disjoint
      (hV.primeIdealOf ⟨x, hx⟩).asIdeal.primeCompl (X.presheaf.stalk x)
      (hV.primeIdealOf ⟨η, hη⟩).asIdeal (hV.primeIdealOf ⟨η, hη⟩).isPrime hdisj
  have hnzd : (X.presheaf.germ V x hx).hom (c.coord j) ∈
      nonZeroDivisors (X.presheaf.stalk x) :=
    IsLocalization.nonZeroDivisors_le_comap (hV.primeIdealOf ⟨x, hx⟩).asIdeal.primeCompl
      (X.presheaf.stalk x) (coord_mem_nonZeroDivisors hV c j)
  have hDx : stalkIdeal D x =
      Ideal.span ({(X.presheaf.germ V x hx).hom (c.coord j)} : Set (X.presheaf.stalk x)) :=
    stalkIdeal_eq_span_germ_coord p hV c j D hD x hx
  have hDη : stalkIdeal D η =
      Ideal.span ({(X.presheaf.germ V η hη).hom (c.coord j)} : Set (X.presheaf.stalk η)) :=
    stalkIdeal_eq_span_germ_coord p hV c j D hD η hη
  have hmaxη : stalkIdeal D η = IsLocalRing.maximalIdeal (X.presheaf.stalk η) :=
    stalkIdeal_eq_maximalIdeal_of_minimal p hV c j D hD x η hx hη hspec hηs hmin
  have hIη : stalkIdeal I η ≤ IsLocalRing.maximalIdeal (X.presheaf.stalk η) ^ a :=
    (le_orderAt_iff I η a).mp ha
  have hmapη : IsLocalRing.maximalIdeal (X.presheaf.stalk η) ^ a =
      Ideal.map (algebraMap (Γ(X, V)) (X.presheaf.stalk η))
        (Ideal.span ({c.coord j ^ a} : Set (Γ(X, V)))) := by
    rw [← hmaxη, hDη, Ideal.span_singleton_pow, Ideal.map_span, halgη]
    simp [Set.image_singleton, map_pow]
  rw [hDx, Ideal.span_singleton_pow, stalkIdeal_eq_map_germ I x ⟨V, hV⟩ hx,
    Ideal.map_le_iff_le_comap]
  intro g hg
  rw [Ideal.mem_comap]
  have hgη : (X.presheaf.germ V η hη).hom g ∈ stalkIdeal I η :=
    germ_mem_stalkIdeal I η ⟨V, hV⟩ hη hg
  have hstep : (X.presheaf.germ V η hη).hom g ∈
      Ideal.map (algebraMap (Γ(X, V)) (X.presheaf.stalk η))
        (Ideal.span ({c.coord j ^ a} : Set (Γ(X, V)))) := by
    rw [← hmapη]
    exact hIη hgη
  obtain ⟨w, hw⟩ := (IsLocalization.mem_map_algebraMap_iff
    (M := (hV.primeIdealOf ⟨η, hη⟩).asIdeal.primeCompl) (S := X.presheaf.stalk η)).mp hstep
  have hw' : algebraMap (Γ(X, V)) (X.presheaf.stalk η) (g * (w.2 : Γ(X, V))) =
      algebraMap (Γ(X, V)) (X.presheaf.stalk η) ((w.1 : Γ(X, V))) := by
    rw [map_mul]
    exact hw
  obtain ⟨cc, hcc⟩ := (IsLocalization.eq_iff_exists
    (M := (hV.primeIdealOf ⟨η, hη⟩).asIdeal.primeCompl)
    (S := X.presheaf.stalk η)).mp hw'
  have humem : ((cc : Γ(X, V)) * (w.2 : Γ(X, V))) ∈
      (hV.primeIdealOf ⟨η, hη⟩).asIdeal.primeCompl := Submonoid.mul_mem _ cc.2 w.2.2
  have hug : ((cc : Γ(X, V)) * (w.2 : Γ(X, V))) * g ∈
      Ideal.span ({c.coord j ^ a} : Set (Γ(X, V))) := by
    have heq : ((cc : Γ(X, V)) * (w.2 : Γ(X, V))) * g = (cc : Γ(X, V)) * (w.1 : Γ(X, V)) := by
      rw [← hcc]
      ring
    rw [heq]
    exact Ideal.mul_mem_left _ _ w.1.2
  have hnotin : (X.presheaf.germ V x hx).hom ((cc : Γ(X, V)) * (w.2 : Γ(X, V))) ∉
      Ideal.span ({(X.presheaf.germ V x hx).hom (c.coord j)} : Set (X.presheaf.stalk x)) := by
    intro hcon
    exact humem (hqle _ hcon)
  obtain ⟨d, hd⟩ := Ideal.mem_span_singleton.mp hug
  have hA : (X.presheaf.germ V x hx).hom ((cc : Γ(X, V)) * (w.2 : Γ(X, V))) *
      (X.presheaf.germ V x hx).hom g ∈
      Ideal.span ({(X.presheaf.germ V x hx).hom (c.coord j) ^ a} : Set (X.presheaf.stalk x)) := by
    refine Ideal.mem_span_singleton.mpr ⟨(X.presheaf.germ V x hx).hom d, ?_⟩
    rw [← map_mul, hd, map_mul, map_pow]
  exact mem_span_pow_of_mul_mem_span_pow _ hprime hnzd a _ _ hnotin hA
end FunctorialResolution.EmbeddedResolution
