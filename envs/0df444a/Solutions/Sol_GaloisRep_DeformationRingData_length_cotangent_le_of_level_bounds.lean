-- Prove2me | solution 1 for GaloisRep.DeformationRingData.length_cotangent_le_of_level_bounds
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:07.331093+00:00
-- url     : https://prove2.me/submissions/ad2cd65d-7e16-5951-a827-52c4c4d70760

import Definitions.Def_GaloisRep_DeformationRingData
import Definitions.Def_GaloisRep_LocalConditions
import Mathlib.RingTheory.Ideal.Cotangent
import Mathlib.RingTheory.Length
import Mathlib.RingTheory.Noetherian.Basic
import Mathlib.RingTheory.Finiteness.Basic
import Mathlib.Algebra.Module.Torsion.Basic
import Mathlib.Algebra.Module.Injective
import Mathlib.RingTheory.DiscreteValuationRing.Basic
import Mathlib.RingTheory.Localization.FractionRing
import Mathlib.RingTheory.Finiteness.Defs
import Mathlib.LinearAlgebra.Span.Basic
import Mathlib.RingTheory.FiniteLength
import Mathlib.LinearAlgebra.BilinearMap
import Mathlib.LinearAlgebra.Quotient.Basic
import Mathlib.LinearAlgebra.Isomorphisms
import Mathlib.RingTheory.Ideal.Operations
import Mathlib.Data.Nat.Lattice
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_GaloisRep_DeformationRingData_length_cotangent_le_of_level_bounds

set_option autoImplicit false

open GaloisRep

namespace COT1

variable {𝒪 : Type} [CommRing 𝒪] [IsDomain 𝒪] [IsDiscreteValuationRing 𝒪]
  [IsAdicComplete (IsLocalRing.maximalIdeal 𝒪) 𝒪]

noncomputable def twAd {A : Type} [CommRing A] [IsLocalRing A] (ρ : GaloisRepAdic A)
    (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) :
    Module.End A ρ.V →ₗ[A] Module.End A ρ.V :=
  (ρ.det σ : A) • {
    toFun := fun f => ρ.ρ σ * f * ρ.ρ σ⁻¹
    map_add' := fun f g => by simp only [mul_add, add_mul]
    map_smul' := fun c f => by
      simp only [Algebra.mul_smul_comm, Algebra.smul_mul_assoc, RingHom.id_apply] }

noncomputable abbrev adZero {A : Type} [CommRing A] [IsLocalRing A] (ρ : GaloisRepAdic A) :
    Submodule A (Module.End A ρ.V) :=
  LinearMap.ker (LinearMap.trace A ρ.V)

noncomputable def adZeroInertiaInv {A : Type} [CommRing A] [IsLocalRing A] (ρ : GaloisRepAdic A)
    (P : ValuationSubring (AlgebraicClosure ℚ)) : Submodule A (Module.End A ρ.V) :=
  adZero ρ ⊓ ⨅ τ ∈ P.inertiaSubgroupIn ℚ, LinearMap.ker (twAd ρ τ - LinearMap.id)

noncomputable def localCotangentTermDenom {A : Type} [CommRing A] [IsLocalRing A]
    (ρ : GaloisRepAdic A) (P : ValuationSubring (AlgebraicClosure ℚ))
    (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) :
    Submodule A (adZeroInertiaInv ρ P) :=
  Submodule.comap (adZeroInertiaInv ρ P).subtype
    ((adZeroInertiaInv ρ P).map (twAd ρ σ - LinearMap.id))

noncomputable def cotangentRelaxKer {ρbar : ResidualGaloisRep (IsLocalRing.ResidueField 𝒪)}
    {𝒟₀ 𝒟' : ∀ ⦃A : Type⦄ [CommRing A] [IsLocalRing A] [Algebra 𝒪 A], GaloisRepAdic A → Prop}
    (D₀ : DeformationRingData 𝒪 ρbar 𝒟₀) (D' : DeformationRingData 𝒪 ρbar 𝒟')
    (θ : D'.R →ₐ[𝒪] D₀.R) (x₀ : D₀.R →ₐ[𝒪] 𝒪) :
    Submodule 𝒪 (RingHom.ker (x₀.comp θ : D'.R →ₐ[𝒪] 𝒪)).Cotangent :=
  LinearMap.ker (Ideal.mapCotangent
    (RingHom.ker (x₀.comp θ : D'.R →ₐ[𝒪] 𝒪)) (RingHom.ker x₀) θ
    (fun r hr => by
      simp only [Ideal.mem_comap, RingHom.mem_ker, AlgHom.coe_comp, Function.comp_apply] at hr ⊢
      exact hr))

def WallCotRung {ρbar : ResidualGaloisRep (IsLocalRing.ResidueField 𝒪)}
    {𝒟₀ 𝒟' : ∀ ⦃A : Type⦄ [CommRing A] [IsLocalRing A] [Algebra 𝒪 A], GaloisRepAdic A → Prop}
    (q : ℕ) (D₀ : DeformationRingData 𝒪 ρbar 𝒟₀) (D' : DeformationRingData 𝒪 ρbar 𝒟')
    (θ : D'.R →ₐ[𝒪] D₀.R) (hθ : IsLocalHom (θ : D'.R →+* D₀.R))
    (_hθρ : (D'.ρ.baseChangeAlong (θ : D'.R →+* D₀.R) hθ).IsEquiv D₀.ρ)
    (x₀ : D₀.R →ₐ[𝒪] 𝒪) (hx₀ : IsLocalHom (x₀ : D₀.R →+* 𝒪)) : Prop :=
  ∀ (P : ValuationSubring (AlgebraicClosure ℚ)) (_hP : P.LiesOverPrime q)
    (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (_hσ : P.IsFrobeniusAt σ q),
    Module.length 𝒪 (RingHom.ker (x₀.comp θ : D'.R →ₐ[𝒪] 𝒪)).Cotangent ≤
      Module.length 𝒪 (RingHom.ker x₀).Cotangent +
        Module.length 𝒪 (adZeroInertiaInv (D₀.ρ.baseChangeAlong (x₀ : D₀.R →+* 𝒪) hx₀) P ⧸
          localCotangentTermDenom (D₀.ρ.baseChangeAlong (x₀ : D₀.R →+* 𝒪) hx₀) P σ)

def WallCotTame {ρbar : ResidualGaloisRep (IsLocalRing.ResidueField 𝒪)}
    {𝒟₀ 𝒟' : ∀ ⦃A : Type⦄ [CommRing A] [IsLocalRing A] [Algebra 𝒪 A], GaloisRepAdic A → Prop}
    (q : ℕ) (D₀ : DeformationRingData 𝒪 ρbar 𝒟₀) (D' : DeformationRingData 𝒪 ρbar 𝒟')
    (θ : D'.R →ₐ[𝒪] D₀.R) (x₀ : D₀.R →ₐ[𝒪] 𝒪) (hx₀ : IsLocalHom (x₀ : D₀.R →+* 𝒪)) : Prop :=
  ∀ (P : ValuationSubring (AlgebraicClosure ℚ)) (_hP : P.LiesOverPrime q)
    (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (_hσ : P.IsFrobeniusAt σ q),
    Module.length 𝒪 (cotangentRelaxKer D₀ D' θ x₀) ≤
      Module.length 𝒪 (adZeroInertiaInv (D₀.ρ.baseChangeAlong (x₀ : D₀.R →+* 𝒪) hx₀) P ⧸
        localCotangentTermDenom (D₀.ρ.baseChangeAlong (x₀ : D₀.R →+* 𝒪) hx₀) P σ)

section AbstractRelax

variable {R' R₀ : Type} [CommRing R'] [CommRing R₀] [Algebra 𝒪 R'] [Algebra 𝒪 R₀]
variable (θ : R' →ₐ[𝒪] R₀) (x₀ : R₀ →ₐ[𝒪] 𝒪)

omit [IsDomain 𝒪] [IsDiscreteValuationRing 𝒪] [IsAdicComplete (IsLocalRing.maximalIdeal 𝒪) 𝒪] in

theorem mapCotangent_surjective_along (hθ : Function.Surjective θ) :
    Function.Surjective (Ideal.mapCotangent
      (RingHom.ker (x₀.comp θ : R' →ₐ[𝒪] 𝒪)) (RingHom.ker x₀) θ
      (fun r hr => by
        simp only [Ideal.mem_comap, RingHom.mem_ker, AlgHom.coe_comp,
          Function.comp_apply] at hr ⊢; exact hr)) := by
  intro y
  obtain ⟨⟨y', hy'⟩, rfl⟩ := Ideal.toCotangent_surjective _ y
  obtain ⟨z, rfl⟩ := hθ y'
  have hz : z ∈ RingHom.ker (x₀.comp θ : R' →ₐ[𝒪] 𝒪) := by
    simpa only [RingHom.mem_ker, AlgHom.coe_comp, Function.comp_apply] using hy'
  exact ⟨Ideal.toCotangent _ ⟨z, hz⟩, by simp [Ideal.mapCotangent_toCotangent]⟩

omit [IsDomain 𝒪] [IsDiscreteValuationRing 𝒪] [IsAdicComplete (IsLocalRing.maximalIdeal 𝒪) 𝒪] in

theorem length_cotangent_eq_add_of_surjective (hθ : Function.Surjective θ) :
    Module.length 𝒪 (RingHom.ker (x₀.comp θ : R' →ₐ[𝒪] 𝒪)).Cotangent =
      Module.length 𝒪 (LinearMap.ker (Ideal.mapCotangent
        (RingHom.ker (x₀.comp θ : R' →ₐ[𝒪] 𝒪)) (RingHom.ker x₀) θ
        (fun r hr => by
          simp only [Ideal.mem_comap, RingHom.mem_ker, AlgHom.coe_comp,
            Function.comp_apply] at hr ⊢; exact hr)) : Submodule 𝒪 _) +
      Module.length 𝒪 (RingHom.ker x₀).Cotangent :=
  Module.length_eq_add_of_exact _ _
    (Submodule.subtype_injective _)
    (mapCotangent_surjective_along θ x₀ hθ)
    (LinearMap.exact_subtype_ker_map _)

end AbstractRelax

theorem wallCotRung_of_wallCotTame {ρbar : ResidualGaloisRep (IsLocalRing.ResidueField 𝒪)}
    {𝒟₀ 𝒟' : ∀ ⦃A : Type⦄ [CommRing A] [IsLocalRing A] [Algebra 𝒪 A], GaloisRepAdic A → Prop}
    (q : ℕ) (D₀ : DeformationRingData 𝒪 ρbar 𝒟₀) (D' : DeformationRingData 𝒪 ρbar 𝒟')
    (θ : D'.R →ₐ[𝒪] D₀.R) (hθ : IsLocalHom (θ : D'.R →+* D₀.R))
    (hθρ : (D'.ρ.baseChangeAlong (θ : D'.R →+* D₀.R) hθ).IsEquiv D₀.ρ)
    (x₀ : D₀.R →ₐ[𝒪] 𝒪) (hx₀ : IsLocalHom (x₀ : D₀.R →+* 𝒪))
    (hθsurj : Function.Surjective θ)
    (htame : WallCotTame q D₀ D' θ x₀ hx₀) :
    WallCotRung q D₀ D' θ hθ hθρ x₀ hx₀ := by
  intro P hP σ hσ
  rw [length_cotangent_eq_add_of_surjective θ x₀ hθsurj, add_comm]
  exact add_le_add le_rfl (htame P hP σ hσ)

end COT1

namespace WCOTFin

variable {𝒪 B : Type} [CommRing 𝒪] [CommRing B] [Algebra 𝒪 B]

theorem smul_cotangent_eq_zero (I : Ideal B) {i : B} (hi : i ∈ I) (m : I.Cotangent) : i • m = 0 := by
  obtain ⟨j, rfl⟩ := I.toCotangent_surjective m
  rw [← map_smul, Ideal.toCotangent_eq_zero, pow_two]
  exact Ideal.mul_mem_mul hi j.2

theorem smul_cotangent_eq (x : B →ₐ[𝒪] 𝒪) (b : B) (m : (RingHom.ker (x : B →+* 𝒪)).Cotangent) :
    b • m = x b • m := by
  have hb : b - algebraMap 𝒪 B (x b) ∈ RingHom.ker (x : B →+* 𝒪) := by
    rw [RingHom.mem_ker, map_sub]
    change x b - x (algebraMap 𝒪 B (x b)) = 0
    rw [AlgHom.commutes, Algebra.algebraMap_self_apply, sub_self]
  have h := smul_cotangent_eq_zero _ hb m
  rwa [sub_smul, sub_eq_zero, algebraMap_smul] at h

theorem finite_cotangent_ker [IsNoetherianRing B] (x : B →ₐ[𝒪] 𝒪) :
    Module.Finite 𝒪 (RingHom.ker (x : B →+* 𝒪)).Cotangent := by
  haveI : Module.Finite B (RingHom.ker (x : B →+* 𝒪)) :=
    Module.Finite.iff_fg.mpr (IsNoetherian.noetherian _)
  haveI : Module.Finite B (RingHom.ker (x : B →+* 𝒪)).Cotangent :=
    Module.Finite.of_surjective _ (RingHom.ker (x : B →+* 𝒪)).toCotangent_surjective
  obtain ⟨S, hS⟩ := Module.Finite.fg_top (R := B) (M := (RingHom.ker (x : B →+* 𝒪)).Cotangent)
  have key : ∀ m : (RingHom.ker (x : B →+* 𝒪)).Cotangent,
      m ∈ Submodule.span B (S : Set (RingHom.ker (x : B →+* 𝒪)).Cotangent) →
        m ∈ Submodule.span 𝒪 (S : Set (RingHom.ker (x : B →+* 𝒪)).Cotangent) := by
    intro m hm
    induction hm using Submodule.span_induction with
    | mem y hy => exact Submodule.subset_span hy
    | zero => exact Submodule.zero_mem _
    | add y z _ _ hy hz => exact Submodule.add_mem _ hy hz
    | smul b y _ hy =>
      rw [smul_cotangent_eq x b y]
      exact Submodule.smul_mem _ _ hy
  refine ⟨⟨S, le_antisymm le_top ?_⟩⟩
  rintro m -
  exact key m (by rw [hS]; trivial)

end WCOTFin

namespace WCOTDev

variable (𝒪 : Type) [CommRing 𝒪] [IsDomain 𝒪] [IsDiscreteValuationRing 𝒪]

abbrev DivCoeff : Type :=
  FractionRing 𝒪 ⧸ LinearMap.range (Algebra.linearMap 𝒪 (FractionRing 𝒪))

variable {𝒪}

theorem divCoeff_isTorsion (ϖ : 𝒪) (hϖ : Irreducible ϖ) (x : DivCoeff 𝒪) :
    ∃ m : ℕ, ϖ ^ m • x = 0 := by
  obtain ⟨f, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  obtain ⟨a, b, hb, rfl⟩ := IsFractionRing.div_surjective (A := 𝒪) f
  have hb0 : b ≠ 0 := nonZeroDivisors.ne_zero hb
  obtain ⟨n, u, rfl⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hb0 hϖ
  refine ⟨n, ?_⟩
  rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero]
  have hu0 : algebraMap 𝒪 (FractionRing 𝒪) (u : 𝒪) ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective 𝒪 _)).mpr (Units.ne_zero u)
  have hϖ0 : algebraMap 𝒪 (FractionRing 𝒪) (ϖ ^ n) ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective 𝒪 _)).mpr (pow_ne_zero n hϖ.ne_zero)
  refine ⟨a * ↑u⁻¹, ?_⟩
  have h1 : algebraMap 𝒪 (FractionRing 𝒪) ↑u⁻¹ = (algebraMap 𝒪 (FractionRing 𝒪) ↑u)⁻¹ :=
    (inv_eq_of_mul_eq_one_right (by rw [← map_mul, Units.mul_inv, map_one])).symm
  rw [Algebra.linearMap_apply, map_mul, h1, Algebra.smul_def, map_mul]
  field_simp

theorem exists_surjective_onto_torsionBy_divCoeff (ϖ : 𝒪) (hϖ : Irreducible ϖ) (m : ℕ) :
    ∃ f : 𝒪 →ₗ[𝒪] Submodule.torsionBy 𝒪 (DivCoeff 𝒪) (ϖ ^ m),
      Function.Surjective f ∧ LinearMap.ker f = Ideal.span {ϖ ^ m} := by
  classical
  set K := FractionRing 𝒪
  have hϖK : algebraMap 𝒪 K (ϖ ^ m) ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective 𝒪 _)).mpr (pow_ne_zero m hϖ.ne_zero)
  set c : K := (algebraMap 𝒪 K (ϖ ^ m))⁻¹ with hc
  set f₀ : 𝒪 →ₗ[𝒪] DivCoeff 𝒪 :=
    (LinearMap.range (Algebra.linearMap 𝒪 K)).mkQ.comp (LinearMap.toSpanSingleton 𝒪 K c)
    with hf₀
  have hf₀a : ∀ a : 𝒪, f₀ a = Submodule.Quotient.mk (a • c) := fun a => rfl
  have hmem : ∀ a : 𝒪, f₀ a ∈ Submodule.torsionBy 𝒪 (DivCoeff 𝒪) (ϖ ^ m) := by
    intro a
    rw [Submodule.mem_torsionBy_iff, hf₀a, ← Submodule.Quotient.mk_smul,
      Submodule.Quotient.mk_eq_zero]
    refine LinearMap.mem_range.mpr ⟨a, ?_⟩
    rw [Algebra.linearMap_apply, smul_smul, Algebra.smul_def, map_mul, hc,
      mul_comm (algebraMap 𝒪 K (ϖ ^ m)), mul_assoc, mul_inv_cancel₀ hϖK, mul_one]
  refine ⟨LinearMap.codRestrict _ f₀ hmem, ?_, ?_⟩
  ·
    rintro ⟨y, hy⟩
    rw [Submodule.mem_torsionBy_iff] at hy
    obtain ⟨g, rfl⟩ := Submodule.Quotient.mk_surjective _ y
    rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero] at hy
    obtain ⟨b, hb⟩ := LinearMap.mem_range.mp hy
    rw [Algebra.linearMap_apply] at hb
    refine ⟨b, Subtype.ext ?_⟩
    simp only [LinearMap.codRestrict_apply]
    rw [hf₀a]
    congr 1
    rw [Algebra.smul_def, hc, hb, Algebra.smul_def,
      mul_comm (algebraMap 𝒪 K (ϖ ^ m)) g, mul_assoc, mul_inv_cancel₀ hϖK, mul_one]
  ·
    ext a
    rw [LinearMap.mem_ker, Ideal.mem_span_singleton]
    constructor
    · intro ha
      have ha' : f₀ a = 0 := by
        have h0 := congrArg Subtype.val ha
        simpa only [LinearMap.codRestrict_apply, ZeroMemClass.coe_zero] using h0
      rw [hf₀a, Submodule.Quotient.mk_eq_zero] at ha'
      obtain ⟨d, hd⟩ := LinearMap.mem_range.mp ha'
      rw [Algebra.linearMap_apply] at hd
      refine ⟨d, ?_⟩
      have h2 : algebraMap 𝒪 K (ϖ ^ m * d) = algebraMap 𝒪 K a := by
        rw [map_mul, hd, Algebra.smul_def, hc, mul_comm (algebraMap 𝒪 K a), ← mul_assoc,
          mul_inv_cancel₀ hϖK, one_mul]
      exact (IsFractionRing.injective 𝒪 K h2).symm
    · rintro ⟨d, rfl⟩
      refine Subtype.ext ?_
      simp only [LinearMap.codRestrict_apply, ZeroMemClass.coe_zero]
      rw [hf₀a, Submodule.Quotient.mk_eq_zero]
      refine LinearMap.mem_range.mpr ⟨d, ?_⟩
      rw [Algebra.linearMap_apply, Algebra.smul_def, map_mul, hc,
        mul_comm (algebraMap 𝒪 K (ϖ ^ m)), mul_assoc, mul_inv_cancel₀ hϖK, mul_one]

theorem injective_divCoeff : Module.Injective 𝒪 (DivCoeff 𝒪) := by
  refine Module.Baer.injective ?_
  intro I g
  obtain ⟨c, rfl⟩ := (IsPrincipalIdealRing.principal I).principal
  by_cases hc : c = 0
  · subst hc
    refine ⟨0, fun x hx => ?_⟩
    have hx0 : x = 0 := by
      obtain ⟨d, rfl⟩ := Submodule.mem_span_singleton.mp hx
      simp
    subst hx0
    have hzero : (⟨(0 : 𝒪), hx⟩ : ↥(Submodule.span 𝒪 {(0 : 𝒪)})) = 0 := rfl
    rw [hzero]
    exact (map_zero g).symm
  · obtain ⟨h, hh⟩ := Submodule.Quotient.mk_surjective _
      (g ⟨c, Submodule.mem_span_singleton_self c⟩)
    have hcK : algebraMap 𝒪 (FractionRing 𝒪) c ≠ 0 :=
      (map_ne_zero_iff _ (IsFractionRing.injective 𝒪 _)).mpr hc
    refine ⟨(LinearMap.range (Algebra.linearMap 𝒪 (FractionRing 𝒪))).mkQ.comp
      (LinearMap.toSpanSingleton 𝒪 _ ((algebraMap 𝒪 (FractionRing 𝒪) c)⁻¹ * h)), ?_⟩
    intro x hx
    obtain ⟨d, rfl⟩ := Submodule.mem_span_singleton.mp hx
    have hsub : (⟨d • c, Submodule.smul_mem _ d (Submodule.mem_span_singleton_self c)⟩ :
        Submodule.span 𝒪 {c}) = d • ⟨c, Submodule.mem_span_singleton_self c⟩ := rfl
    have hgoal : g ⟨d • c, Submodule.smul_mem _ d (Submodule.mem_span_singleton_self c)⟩
        = d • g ⟨c, Submodule.mem_span_singleton_self c⟩ := by
      rw [hsub, map_smul]
    rw [hgoal, ← hh]
    simp only [LinearMap.comp_apply, LinearMap.toSpanSingleton_apply, Submodule.mkQ_apply,
      ← Submodule.Quotient.mk_smul]
    congr 1
    rw [smul_eq_mul, mul_smul]
    congr 1
    rw [Algebra.smul_def, ← mul_assoc, mul_inv_cancel₀ hcK, one_mul]

end WCOTDev

namespace WCOTDev1e

theorem exists_pow_smul_comp_eq_zero {R : Type} [CommRing R] {E M : Type} [AddCommGroup E] [Module R E]
    [AddCommGroup M] [Module R M] [Module.Finite R M] (ϖ : R) (hE : ∀ e : E, ∃ n : ℕ, ϖ ^ n • e = 0)
    (φ : M →ₗ[R] E) : ∃ n : ℕ, ∀ x : M, ϖ ^ n • φ x = 0 := by
  classical
  obtain ⟨s, hs⟩ := Module.Finite.fg_top (R := R) (M := M)
  choose n hn using fun e : E => hE e
  refine ⟨s.sup fun x => n (φ x), fun x => ?_⟩
  let N : Submodule R M :=
    { carrier := {x | ϖ ^ (s.sup fun x => n (φ x)) • φ x = 0}
      add_mem' := fun {a b} ha hb => by
        simp only [Set.mem_setOf_eq, map_add, smul_add] at ha hb ⊢
        rw [ha, hb, add_zero]
      zero_mem' := by simp
      smul_mem' := fun c a ha => by
        simp only [Set.mem_setOf_eq, map_smul] at ha ⊢
        rw [smul_comm, ha, smul_zero] }
  have hgen : (s : Set M) ⊆ N := by
    intro x hx
    have hle : n (φ x) ≤ s.sup fun x => n (φ x) := Finset.le_sup (f := fun x => n (φ x)) hx
    show ϖ ^ (s.sup fun x => n (φ x)) • φ x = 0
    rw [← Nat.sub_add_cancel hle, pow_add, mul_smul, hn (φ x), smul_zero]
  have htop : (⊤ : Submodule R M) ≤ N := by
    rw [← hs]
    exact Submodule.span_le.mpr hgen
  exact htop (Submodule.mem_top : x ∈ ⊤)

end WCOTDev1e

namespace WCOTDev1e

variable {R : Type} [CommRing R] {E : Type} [AddCommGroup E] [Module R E]

theorem exists_linearMap_apply_ne_zero [Module.Injective R E]
    (hE : ∀ m : Ideal R, m.IsMaximal → ∃ f : (R ⧸ m) →ₗ[R] E, f (Submodule.Quotient.mk 1) ≠ 0)
    {M : Type} [AddCommGroup M] [Module R M] (y : M) (hy : y ≠ 0) :
    ∃ ψ : M →ₗ[R] E, ψ y ≠ 0 := by
  let a : Ideal R := LinearMap.ker (LinearMap.toSpanSingleton R M y)
  have ha : a ≠ ⊤ := by
    intro h
    have h1 : (1 : R) ∈ a := h ▸ Submodule.mem_top
    simp only [a, LinearMap.mem_ker, LinearMap.toSpanSingleton_apply, one_smul] at h1
    exact hy h1
  obtain ⟨m, hm, ham⟩ := Ideal.exists_le_maximal a ha
  obtain ⟨f, hf⟩ := hE m hm
  let g : (R ⧸ a) →ₗ[R] E := f.comp (Submodule.mapQ a m LinearMap.id (fun r hr => ham hr))
  let ι : (R ⧸ a) →ₗ[R] M := a.liftQ (LinearMap.toSpanSingleton R M y) le_rfl
  have hι : Function.Injective ι := by
    rw [← LinearMap.ker_eq_bot]
    exact Submodule.ker_liftQ_eq_bot _ _ _ le_rfl
  obtain ⟨ψ, hψ⟩ := Module.Injective.out ι hι g
  refine ⟨ψ, ?_⟩
  have h1 : ι (Submodule.Quotient.mk 1) = y := by
    change (a.liftQ (LinearMap.toSpanSingleton R M y) le_rfl) (Submodule.Quotient.mk 1) = y
    rw [Submodule.liftQ_apply, LinearMap.toSpanSingleton_apply, one_smul]
  rw [← h1, hψ]
  simpa [g, Submodule.mapQ_apply] using hf

theorem length_le_length_linearMap [Module.Injective R E]
    (hE : ∀ m : Ideal R, m.IsMaximal → ∃ f : (R ⧸ m) →ₗ[R] E, f (Submodule.Quotient.mk 1) ≠ 0)
    (K : Type) [AddCommGroup K] [Module R K] :
    Module.length R K ≤ Module.length R (K →ₗ[R] E) := by
  let ann : Submodule R K → Submodule R (K →ₗ[R] E) :=
    fun N => LinearMap.ker (LinearMap.lcomp R E N.subtype)
  have hanti : StrictAnti ann := by
    intro N N' hlt
    refine lt_of_le_of_ne ?_ ?_
    · intro φ hφ
      simp only [ann, LinearMap.mem_ker] at hφ ⊢
      ext x
      have := LinearMap.congr_fun hφ ⟨x, hlt.le x.2⟩
      simpa using this
    · intro heq
      obtain ⟨x, hxN', hxN⟩ := SetLike.exists_of_lt hlt
      have hy : N.mkQ x ≠ 0 := by
        simpa [Submodule.Quotient.mk_eq_zero] using hxN
      obtain ⟨ψ, hψ⟩ := exists_linearMap_apply_ne_zero hE (N.mkQ x) hy
      have hmem : ψ.comp N.mkQ ∈ ann N := by
        simp only [ann, LinearMap.mem_ker]
        ext z
        simp [(Submodule.Quotient.mk_eq_zero N).mpr z.2]
      have hnot : ψ.comp N.mkQ ∉ ann N' := by
        simp only [ann, LinearMap.mem_ker]
        intro h
        apply hψ
        have := LinearMap.congr_fun h ⟨x, hxN'⟩
        simpa using this
      exact hnot (heq ▸ hmem)
  have hdim : Order.krullDim (Submodule R K) ≤ Order.krullDim (Submodule R (K →ₗ[R] E))ᵒᵈ :=
    Order.krullDim_le_of_strictMono (fun N => OrderDual.toDual (ann N)) fun _ _ h => hanti h
  rw [Order.krullDim_orderDual, ← Module.coe_length, ← Module.coe_length] at hdim
  exact_mod_cast hdim

end WCOTDev1e

namespace WCOTWallAE

theorem eq_of_le_of_length_le {R M : Type} [Ring R] [AddCommGroup M] [Module R M]
    {N P : Submodule R M} (hNP : N ≤ P)
    (hlen : Module.length R P ≤ Module.length R N)
    (hfin : Module.length R N ≠ ⊤) : N = P := by
  set N' : Submodule R ↥P := N.comap P.subtype with hN'def
  have hlenN' : Module.length R ↥N' = Module.length R ↥N :=
    (Submodule.comapSubtypeEquivOfLe hNP).length_eq
  have hadd : Module.length R ↥P =
      Module.length R ↥N' + Module.length R (↥P ⧸ N') :=
    Module.length_eq_add_of_exact N'.subtype N'.mkQ (Submodule.subtype_injective _)
      (Submodule.mkQ_surjective _) (LinearMap.exact_subtype_mkQ _)
  have hfin' : Module.length R ↥N' ≠ ⊤ := by rw [hlenN']; exact hfin
  have heq : Module.length R ↥P = Module.length R ↥N' := by
    refine le_antisymm ?_ ?_
    · rw [hlenN']; exact hlen
    · rw [hadd]; exact le_self_add
  have hq0 : Module.length R (↥P ⧸ N') = 0 :=
    (ENat.addLECancellable_of_ne_top hfin').inj.mp (by rw [add_zero, ← hadd]; exact heq)
  have hsub : Subsingleton (↥P ⧸ N') := Module.length_eq_zero_iff.mp hq0
  have hN'top : N' = ⊤ := Submodule.Quotient.subsingleton_iff.mp hsub
  refine le_antisymm hNP fun x hx => ?_
  have hmem : (⟨x, hx⟩ : ↥P) ∈ N' := hN'top ▸ Submodule.mem_top
  simpa [hN'def, Submodule.mem_comap] using hmem

theorem length_le_of_monotone_exhaustive {R M : Type} [Ring R] [AddCommGroup M] [Module R M]
    (A : ℕ → Submodule R M) (hmono : Monotone A)
    (hexh : ∀ x : M, ∃ m, x ∈ A m) (B : ℕ∞)
    (hB : ∀ m, Module.length R (A m) ≤ B) :
    Module.length R M ≤ B := by
  by_cases hBtop : B = ⊤
  · exact hBtop ▸ le_top
  have hfin : ∀ m, Module.length R (A m) ≠ ⊤ :=
    fun m h => hBtop (top_le_iff.mp (h ▸ hB m))
  set f : ℕ → ℕ := fun m => (Module.length R (A m)).toNat with hfdef
  have hbdd : BddAbove (Set.range f) := by
    refine ⟨B.toNat, ?_⟩
    rintro n ⟨m, rfl⟩
    exact ENat.toNat_le_toNat (hB m) hBtop
  obtain ⟨m₀, hm₀⟩ := Nat.sSup_mem (Set.range_nonempty f) hbdd
  have hstab : ∀ m, m₀ ≤ m → A m₀ = A m := by
    intro m hm
    refine eq_of_le_of_length_le (hmono hm) ?_ (hfin m₀)
    calc Module.length R (A m) = ((f m : ℕ) : ℕ∞) := (ENat.coe_toNat (hfin m)).symm
      _ ≤ ((f m₀ : ℕ) : ℕ∞) := by exact_mod_cast hm₀.symm ▸ le_csSup hbdd ⟨m, rfl⟩
      _ = Module.length R (A m₀) := ENat.coe_toNat (hfin m₀)
  have htop : A m₀ = ⊤ := by
    rw [eq_top_iff]
    intro x _
    obtain ⟨m, hm⟩ := hexh x
    rcases le_total m m₀ with h | h
    · exact hmono h hm
    · exact (hstab m h).symm ▸ hm
  calc Module.length R M = Module.length R (A m₀) := by
        rw [htop]; exact Submodule.topEquiv.length_eq.symm
    _ ≤ B := hB m₀

theorem length_submodule_le_of_level_hom_bounds
    {𝒪 : Type} [CommRing 𝒪] [IsDomain 𝒪] [IsDiscreteValuationRing 𝒪]
    {M : Type} [AddCommGroup M] [Module 𝒪 M] [Module.Finite 𝒪 M]
    (K : Submodule 𝒪 M) (B : ℕ∞)
    (hB : ∀ m : ℕ,
      Module.length 𝒪 ((M →ₗ[𝒪] 𝒪 ⧸ (IsLocalRing.maximalIdeal 𝒪) ^ m) ⧸
        LinearMap.ker (LinearMap.lcomp 𝒪 (𝒪 ⧸ (IsLocalRing.maximalIdeal 𝒪) ^ m) K.subtype)) ≤ B) :
    Module.length 𝒪 (↥K) ≤ B := by
  classical
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible 𝒪
  have h𝔪 : IsLocalRing.maximalIdeal 𝒪 = Ideal.span {ϖ} := hϖ.maximalIdeal_eq
  have h𝔪m : ∀ m : ℕ, IsLocalRing.maximalIdeal 𝒪 ^ m = Ideal.span {ϖ ^ m} := fun m => by
    rw [h𝔪, Ideal.span_singleton_pow]
  haveI hEinj : Module.Injective 𝒪 (WCOTDev.DivCoeff 𝒪) := WCOTDev.injective_divCoeff

  have hemb : ∀ m : ℕ, ∃ emb : (𝒪 ⧸ Ideal.span {ϖ ^ m}) →ₗ[𝒪] WCOTDev.DivCoeff 𝒪,
      Function.Injective emb ∧ (∀ z, ϖ ^ m • emb z = 0) ∧
      (∀ g : M →ₗ[𝒪] WCOTDev.DivCoeff 𝒪, (∀ x, ϖ ^ m • g x = 0) →
        ∃ φ : M →ₗ[𝒪] 𝒪 ⧸ Ideal.span {ϖ ^ m}, emb.comp φ = g) := by
    intro m
    obtain ⟨f₀, hf₀surj, hf₀ker⟩ := WCOTDev.exists_surjective_onto_torsionBy_divCoeff ϖ hϖ m
    set emb0 : (𝒪 ⧸ Ideal.span {ϖ ^ m}) →ₗ[𝒪]
        ↥(Submodule.torsionBy 𝒪 (WCOTDev.DivCoeff 𝒪) (ϖ ^ m)) :=
      (Ideal.span {ϖ ^ m}).liftQ f₀ (le_of_eq hf₀ker.symm) with hemb0def
    have hemb0inj : Function.Injective emb0 := by
      rw [← LinearMap.ker_eq_bot]
      exact Submodule.ker_liftQ_eq_bot _ _ _ (le_of_eq hf₀ker)
    have hemb0surj : Function.Surjective emb0 := by
      intro y
      obtain ⟨a, ha⟩ := hf₀surj y
      exact ⟨Submodule.Quotient.mk a, by rw [hemb0def, Submodule.liftQ_apply, ha]⟩
    refine ⟨(Submodule.torsionBy 𝒪 (WCOTDev.DivCoeff 𝒪) (ϖ ^ m)).subtype.comp emb0,
      (Submodule.subtype_injective _).comp hemb0inj, ?_, ?_⟩
    · intro z
      show ϖ ^ m • ((emb0 z : WCOTDev.DivCoeff 𝒪)) = 0
      exact Submodule.mem_torsionBy_iff _ _ |>.mp (emb0 z).2
    · intro g hg
      have hgmem : ∀ x, g x ∈ Submodule.torsionBy 𝒪 (WCOTDev.DivCoeff 𝒪) (ϖ ^ m) :=
        fun x => Submodule.mem_torsionBy_iff _ _ |>.mpr (hg x)
      set e0 : (𝒪 ⧸ Ideal.span {ϖ ^ m}) ≃ₗ[𝒪]
          ↥(Submodule.torsionBy 𝒪 (WCOTDev.DivCoeff 𝒪) (ϖ ^ m)) :=
        LinearEquiv.ofBijective emb0 ⟨hemb0inj, hemb0surj⟩ with he0def
      refine ⟨e0.symm.toLinearMap.comp (LinearMap.codRestrict _ g hgmem), ?_⟩
      ext x
      simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, Submodule.coe_subtype]
      have h1 : emb0 (e0.symm (LinearMap.codRestrict _ g hgmem x)) =
          LinearMap.codRestrict _ g hgmem x := by
        have h2 : ∀ z, emb0 z = e0 z := fun z => rfl
        rw [h2, LinearEquiv.apply_symm_apply]
      rw [h1, LinearMap.codRestrict_apply]

  set 𝒜 : ℕ → Submodule 𝒪 (↥K →ₗ[𝒪] WCOTDev.DivCoeff 𝒪) := fun m =>
    { carrier := {f | ∃ g : M →ₗ[𝒪] WCOTDev.DivCoeff 𝒪,
        (∀ x : M, ϖ ^ m • g x = 0) ∧ f = g.comp K.subtype}
      add_mem' := by
        rintro f₁ f₂ ⟨g₁, hg₁, rfl⟩ ⟨g₂, hg₂, rfl⟩
        exact ⟨g₁ + g₂, fun x => by
          simp only [LinearMap.add_apply, smul_add, hg₁ x, hg₂ x, add_zero],
          (LinearMap.add_comp _ _ _).symm⟩
      zero_mem' := ⟨0, by simp, (LinearMap.zero_comp _).symm⟩
      smul_mem' := by
        rintro c f ⟨g, hg, rfl⟩
        exact ⟨c • g, fun x => by
          rw [LinearMap.smul_apply, smul_comm, hg x, smul_zero],
          (LinearMap.smul_comp _ _ _).symm⟩ } with h𝒜def
  have hmonoA : Monotone 𝒜 := by
    refine monotone_nat_of_le_succ fun m f hf => ?_
    obtain ⟨g, hg, rfl⟩ := hf
    exact ⟨g, fun x => by rw [pow_succ', mul_smul, hg x, smul_zero], rfl⟩
  have hexhA : ∀ f : ↥K →ₗ[𝒪] WCOTDev.DivCoeff 𝒪, ∃ m, f ∈ 𝒜 m := by
    intro f
    obtain ⟨g, hg⟩ := Module.Injective.out K.subtype (Submodule.subtype_injective K) f
    obtain ⟨n, hn⟩ := WCOTDev1e.exists_pow_smul_comp_eq_zero ϖ
      (fun e => WCOTDev.divCoeff_isTorsion ϖ hϖ e) g
    exact ⟨n, g, hn, (LinearMap.ext hg).symm⟩
  have hboundA : ∀ m, Module.length 𝒪 (𝒜 m) ≤ B := by
    intro m
    obtain ⟨emb, hembinj, hembtor, hembfact⟩ := hemb m
    have hBm := hB m
    rw [h𝔪m m] at hBm

    set Ψ : (M →ₗ[𝒪] 𝒪 ⧸ Ideal.span {ϖ ^ m}) →ₗ[𝒪] (↥K →ₗ[𝒪] WCOTDev.DivCoeff 𝒪) :=
      (LinearMap.llcomp 𝒪 ↥K (𝒪 ⧸ Ideal.span {ϖ ^ m}) (WCOTDev.DivCoeff 𝒪) emb).comp
        (LinearMap.lcomp 𝒪 (𝒪 ⧸ Ideal.span {ϖ ^ m}) K.subtype) with hΨdef
    have hΨapply : ∀ φ, Ψ φ = (emb.comp φ).comp K.subtype := fun φ => rfl
    have hrange : LinearMap.range Ψ = 𝒜 m := by
      refine le_antisymm ?_ ?_
      · rintro _ ⟨φ, rfl⟩
        refine ⟨emb.comp φ, fun x => by
          simp only [LinearMap.comp_apply]; exact hembtor (φ x), ?_⟩
        rw [hΨapply]
      · rintro f ⟨g, hg, rfl⟩
        obtain ⟨φ, hφ⟩ := hembfact g hg
        exact ⟨φ, by rw [hΨapply, hφ]⟩
    have hker : LinearMap.ker Ψ =
        LinearMap.ker (LinearMap.lcomp 𝒪 (𝒪 ⧸ Ideal.span {ϖ ^ m}) K.subtype) := by
      ext φ
      simp only [LinearMap.mem_ker]
      constructor
      · intro h0
        have h1 : (emb.comp φ).comp K.subtype = 0 := by rw [← hΨapply]; exact h0
        ext x
        have h2 := LinearMap.congr_fun h1 x
        simp only [LinearMap.comp_apply, LinearMap.zero_apply, LinearMap.lcomp_apply] at h2 ⊢
        exact hembinj (by rw [h2, map_zero])
      · intro h0
        rw [hΨapply]
        ext x
        have h1 := LinearMap.congr_fun h0 x
        simp only [LinearMap.lcomp_apply, LinearMap.comp_apply, LinearMap.zero_apply] at h1 ⊢
        rw [h1, map_zero]
    calc Module.length 𝒪 (𝒜 m)
        = Module.length 𝒪 (LinearMap.range Ψ) := by rw [hrange]
      _ = Module.length 𝒪 ((M →ₗ[𝒪] 𝒪 ⧸ Ideal.span {ϖ ^ m}) ⧸ LinearMap.ker Ψ) :=
          (LinearMap.quotKerEquivRange Ψ).length_eq.symm
      _ = Module.length 𝒪 ((M →ₗ[𝒪] 𝒪 ⧸ Ideal.span {ϖ ^ m}) ⧸
            LinearMap.ker (LinearMap.lcomp 𝒪 (𝒪 ⧸ Ideal.span {ϖ ^ m}) K.subtype)) := by
          rw [hker]
      _ ≤ B := hBm

  have hEdet : ∀ 𝔪' : Ideal 𝒪, 𝔪'.IsMaximal →
      ∃ f : (𝒪 ⧸ 𝔪') →ₗ[𝒪] WCOTDev.DivCoeff 𝒪, f (Submodule.Quotient.mk 1) ≠ 0 := by
    intro 𝔪' h𝔪'
    have h1 : 𝔪' = IsLocalRing.maximalIdeal 𝒪 := IsLocalRing.eq_maximalIdeal h𝔪'
    subst h1
    obtain ⟨emb, hembinj, _, _⟩ := hemb 1
    have hcast : IsLocalRing.maximalIdeal 𝒪 = Ideal.span {ϖ ^ 1} := by
      rw [pow_one, h𝔪]
    rw [hcast]
    refine ⟨emb, fun h0 => ?_⟩
    have h2 : (Submodule.Quotient.mk (1 : 𝒪) : 𝒪 ⧸ Ideal.span {ϖ ^ 1}) = 0 :=
      hembinj (by rw [h0, map_zero])
    rw [Submodule.Quotient.mk_eq_zero, pow_one, Ideal.mem_span_singleton] at h2
    exact hϖ.not_isUnit (isUnit_of_dvd_one h2)
  exact (WCOTDev1e.length_le_length_linearMap hEdet ↥K).trans
    (length_le_of_monotone_exhaustive 𝒜 hmonoA hexhA B hboundA)

end WCOTWallAE

namespace WCOTLadderG

open GaloisRep

theorem length_level_zero_le {𝒪 : Type} [CommRing 𝒪] [IsLocalRing 𝒪]
    {M : Type} [AddCommGroup M] [Module 𝒪 M]
    (K' : Submodule 𝒪 (M →ₗ[𝒪] 𝒪 ⧸ (IsLocalRing.maximalIdeal 𝒪) ^ (0 : ℕ))) (B : ℕ∞) :
    Module.length 𝒪 ((M →ₗ[𝒪] 𝒪 ⧸ (IsLocalRing.maximalIdeal 𝒪) ^ (0 : ℕ)) ⧸ K') ≤ B := by
  haveI : Subsingleton (𝒪 ⧸ (IsLocalRing.maximalIdeal 𝒪) ^ (0 : ℕ)) :=
    Ideal.Quotient.subsingleton_iff.mpr (by rw [pow_zero, Ideal.one_eq_top])
  haveI : Subsingleton (M →ₗ[𝒪] 𝒪 ⧸ (IsLocalRing.maximalIdeal 𝒪) ^ (0 : ℕ)) :=
    ⟨fun f g => LinearMap.ext fun _ => Subsingleton.elim _ _⟩
  haveI : Subsingleton ((M →ₗ[𝒪] 𝒪 ⧸ (IsLocalRing.maximalIdeal 𝒪) ^ (0 : ℕ)) ⧸ K') :=
    ⟨fun u v => by
      obtain ⟨f, rfl⟩ := Submodule.Quotient.mk_surjective K' u
      obtain ⟨g, rfl⟩ := Submodule.Quotient.mk_surjective K' v
      rw [Subsingleton.elim f g]⟩
  rw [Module.length_eq_zero]
  exact bot_le

theorem length_cotangent_le_of_levelwise_bounds
    {𝒪 : Type} [CommRing 𝒪] [IsDomain 𝒪] [IsDiscreteValuationRing 𝒪]
    [IsAdicComplete (IsLocalRing.maximalIdeal 𝒪) 𝒪]
    {ρbar : ResidualGaloisRep (IsLocalRing.ResidueField 𝒪)}
    {𝒟₀ 𝒟' : ∀ ⦃A : Type⦄ [CommRing A] [IsLocalRing A] [Algebra 𝒪 A], GaloisRepAdic A → Prop}
    (D₀ : DeformationRingData 𝒪 ρbar 𝒟₀) (D' : DeformationRingData 𝒪 ρbar 𝒟')
    (θ : D'.R →ₐ[𝒪] D₀.R) (x₀ : D₀.R →ₐ[𝒪] 𝒪) (hθsurj : Function.Surjective θ) (B : ℕ∞)
    (hB : ∀ n : ℕ,
      Module.length 𝒪 (((RingHom.ker (x₀.comp θ : D'.R →ₐ[𝒪] 𝒪)).Cotangent →ₗ[𝒪]
          𝒪 ⧸ (IsLocalRing.maximalIdeal 𝒪) ^ (n + 1)) ⧸
        LinearMap.ker (LinearMap.lcomp 𝒪 (𝒪 ⧸ (IsLocalRing.maximalIdeal 𝒪) ^ (n + 1))
          (COT1.cotangentRelaxKer D₀ D' θ x₀).subtype)) ≤ B) :
    Module.length 𝒪 (RingHom.ker (x₀.comp θ : D'.R →ₐ[𝒪] 𝒪)).Cotangent ≤
      Module.length 𝒪 (RingHom.ker x₀).Cotangent + B := by
  classical
  haveI : Module.Finite 𝒪 (RingHom.ker (x₀.comp θ : D'.R →ₐ[𝒪] 𝒪)).Cotangent :=
    WCOTFin.finite_cotangent_ker (x₀.comp θ)
  have hB' : ∀ m : ℕ,
      Module.length 𝒪 (((RingHom.ker (x₀.comp θ : D'.R →ₐ[𝒪] 𝒪)).Cotangent →ₗ[𝒪]
          𝒪 ⧸ (IsLocalRing.maximalIdeal 𝒪) ^ m) ⧸
        LinearMap.ker (LinearMap.lcomp 𝒪 (𝒪 ⧸ (IsLocalRing.maximalIdeal 𝒪) ^ m)
          (COT1.cotangentRelaxKer D₀ D' θ x₀).subtype)) ≤ B := by
    intro m
    cases m with
    | zero =>
      exact length_level_zero_le
        (LinearMap.ker (LinearMap.lcomp 𝒪 (𝒪 ⧸ (IsLocalRing.maximalIdeal 𝒪) ^ (0 : ℕ))
          (COT1.cotangentRelaxKer D₀ D' θ x₀).subtype)) _
    | succ n =>
      exact hB n
  rw [COT1.length_cotangent_eq_add_of_surjective θ x₀ hθsurj, add_comm]
  refine add_le_add le_rfl ?_
  exact WCOTWallAE.length_submodule_le_of_level_hom_bounds (COT1.cotangentRelaxKer D₀ D' θ x₀) _ hB'

end WCOTLadderG

open GaloisRep

theorem solution
    {𝒪 : Type} [CommRing 𝒪] [IsDomain 𝒪] [IsDiscreteValuationRing 𝒪]
    [IsAdicComplete (IsLocalRing.maximalIdeal 𝒪) 𝒪]
    {ρbar : ResidualGaloisRep (IsLocalRing.ResidueField 𝒪)}
    {𝒟₀ 𝒟' : ∀ ⦃A : Type⦄ [CommRing A] [IsLocalRing A] [Algebra 𝒪 A], GaloisRepAdic A → Prop}
    (D₀ : GaloisRep.DeformationRingData 𝒪 ρbar 𝒟₀) (D' : GaloisRep.DeformationRingData 𝒪 ρbar 𝒟')
    (θ : D'.R →ₐ[𝒪] D₀.R) (x₀ : D₀.R →ₐ[𝒪] 𝒪) (hθsurj : Function.Surjective θ) (B : ℕ∞)
    (hB : ∀ n : ℕ,
      Module.length 𝒪 (((RingHom.ker (x₀.comp θ : D'.R →ₐ[𝒪] 𝒪)).Cotangent →ₗ[𝒪]
        𝒪 ⧸ (IsLocalRing.maximalIdeal 𝒪) ^ (n + 1)) ⧸
      LinearMap.ker (LinearMap.lcomp 𝒪 (𝒪 ⧸ (IsLocalRing.maximalIdeal 𝒪) ^ (n + 1))
        (LinearMap.ker (Ideal.mapCotangent (RingHom.ker (x₀.comp θ : D'.R →ₐ[𝒪] 𝒪))
            (RingHom.ker x₀) θ (fun _ hr => hr))).subtype)) ≤ B) :
    Module.length 𝒪 (RingHom.ker (x₀.comp θ : D'.R →ₐ[𝒪] 𝒪)).Cotangent ≤
      Module.length 𝒪 (RingHom.ker x₀).Cotangent + B := by
  exact WCOTLadderG.length_cotangent_le_of_levelwise_bounds D₀ D' θ x₀ hθsurj B hB

end S_GaloisRep_DeformationRingData_length_cotangent_le_of_level_bounds
end P2MW
export P2MW.S_GaloisRep_DeformationRingData_length_cotangent_le_of_level_bounds (solution)
