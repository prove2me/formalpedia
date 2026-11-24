-- Prove2me | solution 1 for FunctorialResolution.EmbeddedResolution.mem_span_coord_pow_of_mul_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T17:00:34.753842+00:00
-- url     : https://prove2.me/submissions/b6c57a54-e9cd-4032-ace4-aeebe0858da9

import Mathlib
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_Blowup_BlowupProperties
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_IteratedBlowups_ClopenRestriction
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_EtaleCoordinates_ChartRing
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_EtaleCoordinates_CoordinateSubscheme
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_EtaleCoordinates_EtaleChartExistence
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_EtaleCoordinates_StrictNormalCrossings
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_Schemes_IdealSheafData
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_StrongResolution_AffineSpaceSmooth
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_BlowupUniversalProperty
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_ResolutionOfSingularities
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_EtaleCoordinates_CoordinateDivisorSmoothness
import Theorems.Thm_Derivation_liftToLocalization_algebraMap
import Theorems.Thm_Derivation_mapToLocalization_algebraMap
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_EtaleChart_coordRingHom_X
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_EtaleChart_coordRingHom_etale
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_EtaleChart_ofCoords_map
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_EtaleCoordinates_basisDerivation_apply
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_coordVectorInl_inl
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_coordVectorInl_inr
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_coordVectorInr_inl
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_coordVectorInr_inr
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_derivIdealSheafIterate_ideal
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_derivIdealSheafIterate_zero
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_derivIdealSheaf_ideal
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_pullbackCoord_def
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
namespace FunctorialResolution.EmbeddedResolution
variable {X : Scheme.{u}} {k : Type u} [Field k] {p : X ⟶ Spec (CommRingCat.of k)} {m : ℕ}
private theorem mem_span_X_of_X_mul_mem {σ : Type u} {k : Type u} [Field k]
    {j s : σ} (hjs : j ≠ s) (r : MvPolynomial σ k)
    (hr : MvPolynomial.X s * r ∈ Ideal.span {(MvPolynomial.X j : MvPolynomial σ k)}) :
    r ∈ Ideal.span {(MvPolynomial.X j : MvPolynomial σ k)} := by
  classical
  obtain ⟨ψ, hψC, hψXj, hψXi⟩ : ∃ ψ : MvPolynomial σ k →+* MvPolynomial σ k,
      (∀ a : k, ψ (MvPolynomial.C a) = MvPolynomial.C a) ∧
        ψ (MvPolynomial.X j) = 0 ∧
        ∀ i : σ, i ≠ j → ψ (MvPolynomial.X i) = MvPolynomial.X i := by
    refine ⟨MvPolynomial.eval₂Hom (MvPolynomial.C : k →+* MvPolynomial σ k)
        (fun i : σ => if i = j then (0 : MvPolynomial σ k) else MvPolynomial.X i), ?_, ?_, ?_⟩
    · intro a
      simp
    · simp
    · intro i hi
      simp [hi]
  have hXjmem : (MvPolynomial.X j : MvPolynomial σ k)
      ∈ Ideal.span {(MvPolynomial.X j : MvPolynomial σ k)} := Ideal.mem_span_singleton_self _
  have key : (Ideal.Quotient.mk (Ideal.span {(MvPolynomial.X j : MvPolynomial σ k)})).comp ψ
      = Ideal.Quotient.mk (Ideal.span {(MvPolynomial.X j : MvPolynomial σ k)}) := by
    apply MvPolynomial.ringHom_ext
    · intro a
      rw [RingHom.comp_apply, hψC]
    · intro i
      rw [RingHom.comp_apply]
      by_cases h : i = j
      · subst h
        rw [hψXj, map_zero]
        exact (Ideal.Quotient.eq_zero_iff_mem.mpr hXjmem).symm
      · rw [hψXi i h]
  obtain ⟨t, ht⟩ := Ideal.mem_span_singleton.mp hr
  have h0 : ψ (MvPolynomial.X s * r) = 0 := by
    rw [ht, map_mul, hψXj, zero_mul]
  rw [map_mul, hψXi s (Ne.symm hjs)] at h0
  have hXs : (MvPolynomial.X s : MvPolynomial σ k) ≠ 0 := MvPolynomial.X_ne_zero _
  have hψr : ψ r = 0 := by
    rcases mul_eq_zero.mp h0 with h | h
    · exact absurd h hXs
    · exact h
  have h3 := DFunLike.congr_fun key r
  rw [RingHom.comp_apply, hψr, map_zero] at h3
  exact Ideal.Quotient.eq_zero_iff_mem.mp h3.symm
private theorem mem_map_of_mul_mem_of_etale {P A : Type u} [CommRing P] [CommRing A]
    {f : P →+* A} (hf : f.Etale) (I : Ideal P) (w : P)
    (hw : ∀ a b : P ⧸ I,
      (Ideal.Quotient.mk I) w * a = (Ideal.Quotient.mk I) w * b → a = b)
    (x : A) (hx : f w * x ∈ Ideal.map f I) : x ∈ Ideal.map f I := by
  have hg : (Ideal.quotientMap (Ideal.map f I) f Ideal.le_comap_map).Etale :=
    etale_quotientMap hf I
  let _ : Algebra (P ⧸ I) (A ⧸ Ideal.map f I) :=
    (Ideal.quotientMap (Ideal.map f I) f Ideal.le_comap_map).toAlgebra
  have : Algebra.Etale (P ⧸ I) (A ⧸ Ideal.map f I) := hg
  have : Module.Flat (P ⧸ I) (A ⧸ Ideal.map f I) := inferInstance
  have hreg : IsSMulRegular (P ⧸ I) ((Ideal.Quotient.mk I) w) := by
    intro a b h
    exact hw a b (by simpa only [smul_eq_mul] using h)
  have hregB : IsSMulRegular (A ⧸ Ideal.map f I) ((Ideal.Quotient.mk I) w) := hreg.of_flat
  have hy : (Ideal.Quotient.mk I) w • (Ideal.Quotient.mk (Ideal.map f I)) x
      = (Ideal.Quotient.mk I) w • (0 : A ⧸ Ideal.map f I) := by
    rw [smul_zero]
    show (Ideal.quotientMap (Ideal.map f I) f Ideal.le_comap_map) ((Ideal.Quotient.mk I) w) *
        (Ideal.Quotient.mk (Ideal.map f I)) x = 0
    rw [Ideal.quotientMap_mk, ← map_mul]
    exact Ideal.Quotient.eq_zero_iff_mem.mpr hx
  exact Ideal.Quotient.eq_zero_iff_mem.mp (hregB hy)
private theorem X_pow_dvd_of_X_pow_dvd_X_mul {σ : Type u} {k : Type u} [Field k]
    {j s : σ} (hjs : j ≠ s) :
    ∀ (n : ℕ) (r : MvPolynomial σ k),
      (MvPolynomial.X j : MvPolynomial σ k) ^ n ∣ MvPolynomial.X s * r →
        (MvPolynomial.X j : MvPolynomial σ k) ^ n ∣ r := by
  intro n
  induction n with
  | zero =>
    intro r _
    rw [pow_zero]
    exact one_dvd r
  | succ n ih =>
    intro r hr
    have hXne : (MvPolynomial.X j : MvPolynomial σ k) ≠ 0 := MvPolynomial.X_ne_zero _
    have h1 : (MvPolynomial.X j : MvPolynomial σ k) ∣ MvPolynomial.X s * r :=
      dvd_trans (dvd_pow_self _ (Nat.succ_ne_zero n)) hr
    have h2 : (MvPolynomial.X j : MvPolynomial σ k) ∣ r :=
      Ideal.mem_span_singleton.mp
        (mem_span_X_of_X_mul_mem hjs r (Ideal.mem_span_singleton.mpr h1))
    obtain ⟨r', rfl⟩ := h2
    have h3 : (MvPolynomial.X j : MvPolynomial σ k) * MvPolynomial.X j ^ n ∣
        MvPolynomial.X j * (MvPolynomial.X s * r') := by
      have e1 : (MvPolynomial.X j : MvPolynomial σ k) * (MvPolynomial.X s * r')
          = MvPolynomial.X s * (MvPolynomial.X j * r') := by ring
      have e2 : (MvPolynomial.X j : MvPolynomial σ k) * MvPolynomial.X j ^ n
          = MvPolynomial.X j ^ (n + 1) := by ring
      rw [e1, e2]
      exact hr
    have h4 : (MvPolynomial.X j : MvPolynomial σ k) ^ n ∣ MvPolynomial.X s * r' :=
      (mul_dvd_mul_iff_left hXne).mp h3
    have h5 := ih r' h4
    have e3 : (MvPolynomial.X j : MvPolynomial σ k) ^ (n + 1)
        = MvPolynomial.X j * MvPolynomial.X j ^ n := by ring
    rw [e3]
    exact mul_dvd_mul_left _ h5
private theorem eq_of_mk_X_mul_eq_quotient_span_X_pow {σ : Type u} {k : Type u} [Field k]
    {j s : σ} (hjs : j ≠ s) (n : ℕ)
    (a b : MvPolynomial σ k ⧸ Ideal.span {(MvPolynomial.X j : MvPolynomial σ k) ^ n})
    (h : (Ideal.Quotient.mk (Ideal.span {(MvPolynomial.X j : MvPolynomial σ k) ^ n}))
            (MvPolynomial.X s) * a
        = (Ideal.Quotient.mk (Ideal.span {(MvPolynomial.X j : MvPolynomial σ k) ^ n}))
            (MvPolynomial.X s) * b) : a = b := by
  obtain ⟨a', rfl⟩ := Ideal.Quotient.mk_surjective a
  obtain ⟨b', rfl⟩ := Ideal.Quotient.mk_surjective b
  rw [← map_mul, ← map_mul, Ideal.Quotient.eq, ← mul_sub] at h
  exact Ideal.Quotient.eq.mpr (Ideal.mem_span_singleton.mpr
    (X_pow_dvd_of_X_pow_dvd_X_mul hjs n (a' - b') (Ideal.mem_span_singleton.mp h)))
end FunctorialResolution.EmbeddedResolution
end

set_option autoImplicit false
universe u
open CategoryTheory Opposite AlgebraicGeometry TopologicalSpace
open FunctorialResolution FunctorialResolution.EmbeddedResolution
variable {X : Scheme.{u}} {k : Type u} [Field k] {p : X ⟶ Spec (CommRingCat.of k)} {m : ℕ}
namespace FunctorialResolution.EmbeddedResolution
theorem _root_.solution {U : X.Opens} (hU : IsAffineOpen U) (c : EtaleChart p U m)
    {j s : Fin m} (hjs : j ≠ s) (n : ℕ) (x : ↑(X.presheaf.obj (op U)))
    (hx : c.coord s * x ∈ Ideal.span {c.coord j ^ n}) :
    x ∈ Ideal.span {c.coord j ^ n} := by
  classical
  have hmapspan : Ideal.map c.coordRingHom
      (Ideal.span {(MvPolynomial.X (ULift.up j) : MvPolynomial (ULift.{u} (Fin m)) k) ^ n})
      = Ideal.span {c.coord j ^ n} := by
    rw [Ideal.map_span, Set.image_singleton, map_pow, c.coordRingHom_X]
  have hju : (ULift.up j : ULift.{u} (Fin m)) ≠ ULift.up s := by
    intro h
    exact hjs (congrArg ULift.down h)
  have hu : ∀ a b : MvPolynomial (ULift.{u} (Fin m)) k ⧸
        Ideal.span {(MvPolynomial.X (ULift.up j) : MvPolynomial (ULift.{u} (Fin m)) k) ^ n},
      (Ideal.Quotient.mk
          (Ideal.span {(MvPolynomial.X (ULift.up j) : MvPolynomial (ULift.{u} (Fin m)) k) ^ n}))
          (MvPolynomial.X (ULift.up s)) * a
        = (Ideal.Quotient.mk
          (Ideal.span {(MvPolynomial.X (ULift.up j) : MvPolynomial (ULift.{u} (Fin m)) k) ^ n}))
          (MvPolynomial.X (ULift.up s)) * b → a = b :=
    fun a b h => eq_of_mk_X_mul_eq_quotient_span_X_pow hju n a b h
  have hx' : c.coordRingHom (MvPolynomial.X (ULift.up s)) * x
      ∈ Ideal.map c.coordRingHom
          (Ideal.span
            {(MvPolynomial.X (ULift.up j) : MvPolynomial (ULift.{u} (Fin m)) k) ^ n}) := by
    rw [hmapspan, c.coordRingHom_X]
    exact hx
  have hfin := mem_map_of_mul_mem_of_etale (c.coordRingHom_etale hU)
      (Ideal.span {(MvPolynomial.X (ULift.up j) : MvPolynomial (ULift.{u} (Fin m)) k) ^ n})
      (MvPolynomial.X (ULift.up s)) hu x hx'
  rw [hmapspan] at hfin
  exact hfin
end FunctorialResolution.EmbeddedResolution
