-- Prove2me | solution 1 for GaloisRep.DeformationRingData.length_level_quotient_le_of_isUnramifiedAt
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:07.331093+00:00
-- url     : https://prove2.me/submissions/6708d6e3-f378-5b7c-afad-280cd5701ee6

import Definitions.Def_GaloisRep_DeformationRingData
import Definitions.Def_GaloisRep_LocalConditions
import Mathlib.RingTheory.Ideal.Cotangent
import Mathlib.RingTheory.Length
import Mathlib.RingTheory.Noetherian.Basic
import Mathlib.RingTheory.Finiteness.Basic
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Fin.VecNotation
import Mathlib.LinearAlgebra.Matrix.Adjugate
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.LinearAlgebra.FreeModule.PID
import Mathlib.LinearAlgebra.FreeModule.Finite.Quotient
import Mathlib.LinearAlgebra.Determinant
import Mathlib.RingTheory.OrderOfVanishing.Basic
import Mathlib.RingTheory.FiniteLength
import Mathlib.RingTheory.Ideal.Quotient.Operations
import Mathlib.RingTheory.DiscreteValuationRing.Basic
import Mathlib.RingTheory.KrullDimension.PID
import Mathlib.RingTheory.PrincipalIdealDomain
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Ring
import Mathlib.Algebra.Group.Subgroup.Basic
import Mathlib.LinearAlgebra.Isomorphisms
import Mathlib.LinearAlgebra.Quotient.Basic
import Mathlib.Tactic.Group
import Mathlib.Algebra.Module.Torsion.Basic
import Mathlib.Algebra.Module.Injective
import Mathlib.RingTheory.Localization.FractionRing
import Mathlib.RingTheory.Finiteness.Defs
import Mathlib.LinearAlgebra.Span.Basic
import Mathlib.LinearAlgebra.BilinearMap
import Mathlib.RingTheory.Ideal.Operations
import Mathlib.Data.Nat.Lattice
import Definitions.Def_FLTPrelim_Ramification
import Mathlib.RingTheory.LocalRing.ResidueField.Basic
import Mathlib.Algebra.Ring.GeomSum
import Mathlib.RingTheory.Coprime.Lemmas
import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots
import Mathlib.RingTheory.RootsOfUnity.AlgebraicallyClosed
import Mathlib.FieldTheory.Galois.Basic
import Mathlib.FieldTheory.Galois.Infinite
import Mathlib.FieldTheory.KrullTopology
import Mathlib.RingTheory.Valuation.RamificationGroup
import Mathlib.Topology.Algebra.OpenSubgroup
import Mathlib.Topology.Algebra.ClopenNhdofOne
import Mathlib.GroupTheory.OrderOfElement
import Mathlib.FieldTheory.KummerExtension
import Mathlib.GroupTheory.Perm.Cycle.Type
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Valuation.Integral
import Mathlib.FieldTheory.IsAlgClosed.Basic
import Mathlib.RingTheory.Valuation.ValuationSubring
import Mathlib.Algebra.Polynomial.FieldDivision
import Mathlib.RingTheory.Algebraic.Basic
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Algebra.Algebra.Rat
import Mathlib.RingTheory.Valuation.Basic
import Mathlib.RingTheory.Localization.Integral
import Mathlib.RingTheory.Polynomial.Content
import Mathlib.RingTheory.Finiteness.Cardinality
import Mathlib.RingTheory.IntegralClosure.IsIntegral.Basic
import Mathlib.Algebra.Algebra.ZMod
import Mathlib.Algebra.CharP.Basic
import Mathlib.Data.Fintype.Pigeonhole
import Mathlib.Data.ZMod.Basic
import Mathlib.Algebra.Field.ZMod
import Mathlib.Data.Int.GCD
import Mathlib.FieldTheory.Galois.Profinite
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import Mathlib.Algebra.TrivSqZeroExt.Basic
import Mathlib.RingTheory.Finiteness.Prod
import Mathlib.RingTheory.AdicCompletion.Noetherian
import Mathlib.RingTheory.Artinian.Module
import Mathlib.RingTheory.HopkinsLevitzki
import Mathlib.RingTheory.LocalRing.Quotient
import Mathlib.RingTheory.Ideal.Quotient.Noetherian
import Definitions.Def_GaloisRep_Adic
import Mathlib.LinearAlgebra.Charpoly.ToMatrix
import Mathlib.LinearAlgebra.Matrix.Charpoly.Coeff
import Mathlib.RingTheory.Filtration
import Theorems.Thm_Module_length_quotient_le_of_inertia_additive_family
import Theorems.Thm_GaloisRepAdic_det_eq_one_of_mem_inertiaSubgroupIn
import Theorems.Thm_ValuationSubring_mem_inertiaSubgroupIn_pointwise_smul_iff
import Theorems.Thm_GaloisRep_DeformationRingData_exists_algHom_comp_eq_of_isOfType
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_GaloisRep_DeformationRingData_length_level_quotient_le_of_isUnramifiedAt

set_option Elab.async false

open scoped Pointwise

set_option autoImplicit false

open GaloisRep

namespace COT1

variable {𝒪 : Type} [CommRing 𝒪] [IsDomain 𝒪] [IsDiscreteValuationRing 𝒪]
  [IsAdicComplete (IsLocalRing.maximalIdeal 𝒪) 𝒪]

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

end COT1

namespace WCOTInertiaConj

variable {K L : Type} [Field K] [Field L] [Algebra K L]

theorem forall_inertia_eq_zero_of_conj {M : Type} [Zero M] {q : ℕ} (P : ValuationSubring L)
    (hconj : ∀ P' : ValuationSubring L, P'.LiesOverPrime q → ∃ g : L ≃ₐ[K] L, g • P = P')
    (Λ : (L ≃ₐ[K] L) → M)
    (hΛconj : ∀ (g τ : L ≃ₐ[K] L), τ ∈ P.inertiaSubgroupIn K → Λ τ = 0 → Λ (g * τ * g⁻¹) = 0)
    (h0 : ∀ τ ∈ P.inertiaSubgroupIn K, Λ τ = 0) :
    ∀ P' : ValuationSubring L, P'.LiesOverPrime q → ∀ τ ∈ P'.inertiaSubgroupIn K, Λ τ = 0 := by
  intro P' hP' τ hτ
  obtain ⟨g, rfl⟩ := hconj P' hP'
  have hτ' : g⁻¹ * τ * g ∈ P.inertiaSubgroupIn K :=
    (ValuationSubring.mem_inertiaSubgroupIn_pointwise_smul_iff g τ P).mp hτ
  have h := hΛconj g _ hτ' (h0 _ hτ')
  have e : g * (g⁻¹ * τ * g) * g⁻¹ = τ := by group
  rw [e] at h
  exact h

end WCOTInertiaConj

namespace WCOTTameQbar

theorem isUnit_natCast_of_coprime_of_mem {R : Type} [CommRing R] [IsLocalRing R] {p q : ℕ}
    (hcop : Nat.Coprime p q) (hp : (p : R) ∈ IsLocalRing.maximalIdeal R) : IsUnit (q : R) := by
  by_contra hq
  have hqm : (q : R) ∈ IsLocalRing.maximalIdeal R := (IsLocalRing.mem_maximalIdeal _).mpr hq
  obtain ⟨u, v, huv⟩ := (Nat.Coprime.cast (R := R) hcop)
  have h1 : (1 : R) ∈ IsLocalRing.maximalIdeal R := by
    rw [← huv]
    exact Ideal.add_mem _ (Ideal.mul_mem_left _ _ hp) (Ideal.mul_mem_left _ _ hqm)
  exact (IsLocalRing.maximalIdeal.isMaximal R).ne_top ((Ideal.eq_top_iff_one _).mpr h1)

end WCOTTameQbar

open TrivSqZeroExt

local notation "tsze" => TrivSqZeroExt

namespace WCOTTameD

section LiftAlgHom

variable {𝒪 : Type*} [CommRing 𝒪] {B : Type*} [CommRing B] [Algebra 𝒪 B]
  (x : B →ₐ[𝒪] 𝒪) {M : Type*} [AddCommGroup M] [Module 𝒪 M]
  [Module 𝒪ᵐᵒᵖ M] [IsCentralScalar 𝒪 M]

def δ (r : B) : RingHom.ker (x : B →+* 𝒪) :=
  ⟨r - algebraMap 𝒪 B (x r), by
    rw [RingHom.mem_ker, map_sub, sub_eq_zero]
    exact (x.commutes (x r)).symm⟩

theorem coe_δ (r : B) : (δ x r : B) = r - algebraMap 𝒪 B (x r) := rfl

theorem δ_add (r s : B) : δ x (r + s) = δ x r + δ x s := by
  ext; simp only [coe_δ, map_add, AddMemClass.coe_add]; ring

theorem δ_algebraMap (c : 𝒪) : δ x (algebraMap 𝒪 B c) = 0 := by
  ext; simp [coe_δ, AlgHom.commutes]

theorem δ_one : δ x 1 = 0 := by
  have := δ_algebraMap x 1; rwa [map_one] at this

theorem coe_δ_mul (r s : B) :
    (δ x (r * s) : B) = r * (δ x s : B) + s * (δ x r : B) - (δ x r : B) * (δ x s : B) := by
  simp only [coe_δ, map_mul]; ring

theorem toCotangent_δ_mul (r s : B) :
    (RingHom.ker (x : B →+* 𝒪)).toCotangent (δ x (r * s)) =
      (x r) • (RingHom.ker (x : B →+* 𝒪)).toCotangent (δ x s) +
        (x s) • (RingHom.ker (x : B →+* 𝒪)).toCotangent (δ x r) := by
  set I := RingHom.ker (x : B →+* 𝒪)

  have hscalar : ∀ (b : B) (c : I.Cotangent),
      algebraMap 𝒪 B (x b) • c = b • c := by
    intro b c
    obtain ⟨s₀, rfl⟩ := I.toCotangent_surjective c
    have hkill : (δ x b : B) • I.toCotangent s₀ = 0 := by
      rw [← map_smul, show (δ x b : B) • s₀ = ⟨(δ x b : B) * s₀, I.mul_mem_left _ s₀.2⟩ from rfl]
      exact (I.toCotangent_eq_zero _).mpr (by
        rw [pow_two]; exact Ideal.mul_mem_mul (δ x b).2 s₀.2)
    have hb : b = algebraMap 𝒪 B (x b) + (δ x b : B) := by simp [coe_δ]
    conv_rhs => rw [hb, add_smul, hkill, add_zero]

  have hrhs : I.toCotangent (δ x (r * s)) = r • I.toCotangent (δ x s) + s • I.toCotangent (δ x r) := by
    rw [← map_smul, ← map_smul, ← map_add, I.toCotangent_eq]
    refine (Ideal.neg_mem_iff _).mp ?_
    have hmem : ((δ x r : B) * (δ x s : B)) ∈ I ^ 2 := by
      rw [pow_two]; exact Ideal.mul_mem_mul (δ x r).2 (δ x s).2
    convert hmem using 1
    have h1 : (r • δ x s : I) = ⟨r * (δ x s : B), I.mul_mem_left _ (δ x s).2⟩ := rfl
    have h2 : (s • δ x r : I) = ⟨s * (δ x r : B), I.mul_mem_left _ (δ x r).2⟩ := rfl
    have h3 : (δ x (r * s) : B) = r * (δ x s : B) + s * (δ x r : B) - (δ x r : B) * (δ x s : B) :=
      coe_δ_mul x r s
    show -((δ x (r * s) : B) - ((r • δ x s : I) + (s • δ x r : I) : B)) = (δ x r : B) * (δ x s : B)
    rw [h1, h2, h3]; push_cast; ring
  rw [hrhs, ← hscalar r, ← hscalar s, algebraMap_smul, algebraMap_smul]

variable (φ : (RingHom.ker (x : B →+* 𝒪)).Cotangent →ₗ[𝒪] M)

noncomputable def liftAlgHom : B →ₐ[𝒪] tsze 𝒪 M where
  toFun r := (x r, φ ((RingHom.ker (x : B →+* 𝒪)).toCotangent (δ x r)))
  map_one' := by
    ext
    · simp
    · simp [δ_one]
  map_mul' r s := by
    ext
    · simp [fst_mul]
    · simp only [snd_mk, snd_mul, fst_mk, toCotangent_δ_mul x r s, map_add, map_smul,
        op_smul_eq_smul]
  map_zero' := by
    ext
    · simp
    · simp [show δ x 0 = 0 from by ext; simp [coe_δ]]
  map_add' r s := by
    ext
    · simp
    · simp [δ_add]
  commutes' c := by
    ext
    · simp [algebraMap_eq_inl]
    · simp [δ_algebraMap, algebraMap_eq_inl]

@[scoped simp] theorem fst_liftAlgHom (r : B) : (liftAlgHom x φ r).fst = x r := rfl

@[scoped simp] theorem snd_liftAlgHom (r : B) :
    (liftAlgHom x φ r).snd = φ ((RingHom.ker (x : B →+* 𝒪)).toCotangent (δ x r)) := rfl

theorem fstHom_comp_liftAlgHom :
    (fstHom 𝒪 𝒪 M).comp (liftAlgHom x φ) = x := by
  ext r; rfl

end LiftAlgHom

section ModuleFinite

variable {𝒪 : Type*} [CommRing 𝒪] (M : Type*) [AddCommGroup M] [Module 𝒪 M]
  [Module 𝒪ᵐᵒᵖ M] [IsCentralScalar 𝒪 M] [Module.Finite 𝒪 M]

noncomputable def tszeLinearEquivProd : tsze 𝒪 M ≃ₗ[𝒪] 𝒪 × M :=
  LinearEquiv.refl 𝒪 (𝒪 × M)

scoped instance : Module.Finite 𝒪 (tsze 𝒪 M) :=
  Module.Finite.equiv (tszeLinearEquivProd M).symm

end ModuleFinite

section LambdaDef

variable {𝒪 : Type} [CommRing 𝒪] {B : Type} [CommRing B] [Algebra 𝒪 B]
  (x : B →ₐ[𝒪] 𝒪)

noncomputable def cotOfEntry : B →ₗ[𝒪] (RingHom.ker (x : B →+* 𝒪)).Cotangent where
  toFun r := (RingHom.ker (x : B →+* 𝒪)).toCotangent (δ x r)
  map_add' r s := by rw [δ_add, map_add]
  map_smul' c r := by
    simp only [RingHom.id_apply]
    have h0 : (δ x (c • r) : B) = algebraMap 𝒪 B c * (δ x r : B) := by
      simp only [coe_δ, Algebra.smul_def, map_mul, x.commutes,
        Algebra.algebraMap_self, RingHom.id_apply]
      ring
    have h1 : δ x (c • r) = algebraMap 𝒪 B c • δ x r := Subtype.ext h0
    rw [h1, LinearMapClass.map_smul, algebraMap_smul]

theorem cotOfEntry_apply (r : B) :
    cotOfEntry x r = (RingHom.ker (x : B →+* 𝒪)).toCotangent (δ x r) := rfl

theorem snd_liftAlgHom_eq_cotOfEntry {M : Type*} [AddCommGroup M] [Module 𝒪 M]
    [Module 𝒪ᵐᵒᵖ M] [IsCentralScalar 𝒪 M]
    (φ : (RingHom.ker (x : B →+* 𝒪)).Cotangent →ₗ[𝒪] M) (r : B) :
    (liftAlgHom x φ r).snd = φ (cotOfEntry x r) := rfl

variable {V : Type} [AddCommGroup V] [Module B V] (b : Module.Basis (Fin 2) B V)
  (G : Type) (ρ : G → V →ₗ[B] V)

noncomputable def Λₗ {M : Type} [AddCommGroup M] [Module 𝒪 M] :
    ((RingHom.ker (x : B →+* 𝒪)).Cotangent →ₗ[𝒪] M) →ₗ[𝒪] (G → Matrix (Fin 2) (Fin 2) M) where
  toFun φ := fun g => (LinearMap.toMatrix b b (ρ g)).map (fun r => φ (cotOfEntry x r))
  map_add' φ ψ := by
    funext g; ext i j
    simp only [Matrix.map_apply, LinearMap.add_apply, Pi.add_apply, Matrix.add_apply]
  map_smul' c φ := by
    funext g; ext i j
    simp only [Matrix.map_apply, LinearMap.smul_apply, RingHom.id_apply, Pi.smul_apply,
      Matrix.smul_apply]

theorem Λₗ_apply {M : Type} [AddCommGroup M] [Module 𝒪 M]
    (φ : (RingHom.ker (x : B →+* 𝒪)).Cotangent →ₗ[𝒪] M) (g : G) (i j : Fin 2) :
    Λₗ x b G ρ φ g i j = φ (cotOfEntry x ((LinearMap.toMatrix b b (ρ g)) i j)) := rfl

noncomputable def Fbar (M : Type) [CommRing M] [Algebra 𝒪 M] (g : G) :
    Matrix (Fin 2) (Fin 2) M :=
  (LinearMap.toMatrix b b (ρ g)).map ((algebraMap 𝒪 M).comp (x : B →+* 𝒪))

theorem Fbar_apply (M : Type) [CommRing M] [Algebra 𝒪 M] (g : G) (i j : Fin 2) :
    Fbar x b G ρ M g i j = algebraMap 𝒪 M (x ((LinearMap.toMatrix b b (ρ g)) i j)) := rfl

theorem Λₗ_map_mul' [Mul G] {M : Type} [CommRing M] [Algebra 𝒪 M]
    (hρ : ∀ g₁ g₂, ρ (g₁ * g₂) = ρ g₁ ∘ₗ ρ g₂)
    (φ : (RingHom.ker (x : B →+* 𝒪)).Cotangent →ₗ[𝒪] M) (g₁ g₂ : G) :
    Λₗ x b G ρ φ (g₁ * g₂) =
      Fbar x b G ρ M g₁ * Λₗ x b G ρ φ g₂ + Λₗ x b G ρ φ g₁ * Fbar x b G ρ M g₂ := by
  ext i j
  simp only [Λₗ_apply, Matrix.add_apply, Matrix.mul_apply, Fbar_apply,
    hρ, LinearMap.toMatrix_comp b b b, Matrix.mul_apply]
  rw [show cotOfEntry x (∑ k, LinearMap.toMatrix b b (ρ g₁) i k * LinearMap.toMatrix b b (ρ g₂) k j)
      = ∑ k, cotOfEntry x (LinearMap.toMatrix b b (ρ g₁) i k * LinearMap.toMatrix b b (ρ g₂) k j)
    from map_sum (cotOfEntry x) _ _]
  simp only [cotOfEntry_apply, toCotangent_δ_mul, map_sum, map_add, map_smul, Algebra.smul_def]
  rw [Finset.sum_add_distrib]
  refine congrArg₂ _ ?_ ?_ <;> exact Finset.sum_congr rfl (fun k _ => by ring)

theorem Λₗ_map_one [One G] {M : Type} [AddCommGroup M] [Module 𝒪 M] (hρ1 : ρ 1 = LinearMap.id)
    (φ : (RingHom.ker (x : B →+* 𝒪)).Cotangent →ₗ[𝒪] M) :
    Λₗ x b G ρ φ 1 = 0 := by
  ext i j
  simp only [Λₗ_apply, hρ1, LinearMap.toMatrix_id, Matrix.zero_apply]
  rcases eq_or_ne i j with rfl | hij
  · simp only [Matrix.one_apply_eq, cotOfEntry_apply, δ_one, map_zero]
  · simp only [Matrix.one_apply_ne hij, map_zero]

section MonoidHom

variable [Group G] (ρhom : G →* (V →ₗ[B] V))

theorem Λₗ_hadd' {M : Type} [CommRing M] [Algebra 𝒪 M]
    (φ : (RingHom.ker (x : B →+* 𝒪)).Cotangent →ₗ[𝒪] M)
    (τ₁ τ₂ : G) (h1 : Fbar x b G ρhom M τ₁ = 1) (h2 : Fbar x b G ρhom M τ₂ = 1) :
    Λₗ x b G ρhom φ (τ₁ * τ₂) = Λₗ x b G ρhom φ τ₁ + Λₗ x b G ρhom φ τ₂ := by
  rw [Λₗ_map_mul' x b G ρhom (fun _ _ => ρhom.map_mul _ _) φ, h1, h2, one_mul, mul_one, add_comm]

theorem Λₗ_conj_of_fbar_eq_one {M : Type} [CommRing M] [Algebra 𝒪 M]
    (φ : (RingHom.ker (x : B →+* 𝒪)).Cotangent →ₗ[𝒪] M)
    (g τ : G) (hτ : Fbar x b G ρhom M τ = 1) :
    Λₗ x b G ρhom φ (g * τ * g⁻¹) =
      Fbar x b G ρhom M g * Λₗ x b G ρhom φ τ * Fbar x b G ρhom M g⁻¹ := by
  have hρmul : ∀ g₁ g₂, (ρhom : G → V →ₗ[B] V) (g₁ * g₂) = ρhom g₁ ∘ₗ ρhom g₂ :=
    fun _ _ => ρhom.map_mul _ _
  have hcancel : Fbar x b G ρhom M g * Λₗ x b G ρhom φ g⁻¹ +
      Λₗ x b G ρhom φ g * Fbar x b G ρhom M g⁻¹ = 0 := by
    rw [← Λₗ_map_mul' x b G ρhom hρmul φ g g⁻¹, mul_inv_cancel,
      Λₗ_map_one x b G ρhom ρhom.map_one φ]
  have hFτg : Fbar x b G ρhom M (τ * g⁻¹) = Fbar x b G ρhom M g⁻¹ := by
    show ((algebraMap 𝒪 M).comp (x : B →+* 𝒪)).mapMatrix
        (LinearMap.toMatrix b b ((ρhom : G → V →ₗ[B] V) (τ * g⁻¹))) = _
    rw [show (ρhom : G → V →ₗ[B] V) (τ * g⁻¹) = ρhom τ ∘ₗ ρhom g⁻¹ from ρhom.map_mul _ _,
      LinearMap.toMatrix_comp b b b, map_mul]
    show Fbar x b G (⇑ρhom) M τ * Fbar x b G (⇑ρhom) M g⁻¹ = Fbar x b G (⇑ρhom) M g⁻¹
    rw [hτ, one_mul]
  rw [mul_assoc g τ g⁻¹, Λₗ_map_mul' x b G ρhom hρmul φ g (τ * g⁻¹),
    Λₗ_map_mul' x b G ρhom hρmul φ τ g⁻¹, hτ, one_mul, hFτg, mul_add, add_right_comm, hcancel,
    zero_add, mul_assoc]

theorem Λₗ_conj_eq_zero {M : Type} [CommRing M] [Algebra 𝒪 M]
    (φ : (RingHom.ker (x : B →+* 𝒪)).Cotangent →ₗ[𝒪] M)
    (g τ : G) (hτ : Fbar x b G ρhom M τ = 1) (h0 : Λₗ x b G ρhom φ τ = 0) :
    Λₗ x b G ρhom φ (g * τ * g⁻¹) = 0 := by
  rw [Λₗ_conj_of_fbar_eq_one x b G ρhom φ g τ hτ, h0, mul_zero, zero_mul]

theorem trace_Λₗ_eq_of_fbar_eq_one {M : Type} [CommRing M] [Algebra 𝒪 M]
    (φ : (RingHom.ker (x : B →+* 𝒪)).Cotangent →ₗ[𝒪] M)
    (τ : G) (hτ : Fbar x b G ρhom M τ = 1) :
    Matrix.trace (Λₗ x b G ρhom φ τ) =
      φ (cotOfEntry x (Matrix.det (LinearMap.toMatrix b b (ρhom τ)))) := by
  have h00 : algebraMap 𝒪 M (x (LinearMap.toMatrix b b (ρhom τ) 0 0)) = 1 := by
    have := congrFun (congrFun hτ 0) 0; simpa [Fbar_apply, Matrix.one_apply] using this
  have h11 : algebraMap 𝒪 M (x (LinearMap.toMatrix b b (ρhom τ) 1 1)) = 1 := by
    have := congrFun (congrFun hτ 1) 1; simpa [Fbar_apply, Matrix.one_apply] using this
  have h01 : algebraMap 𝒪 M (x (LinearMap.toMatrix b b (ρhom τ) 0 1)) = 0 := by
    have := congrFun (congrFun hτ 0) 1; simpa [Fbar_apply, Matrix.one_apply] using this
  have h10 : algebraMap 𝒪 M (x (LinearMap.toMatrix b b (ρhom τ) 1 0)) = 0 := by
    have := congrFun (congrFun hτ 1) 0; simpa [Fbar_apply, Matrix.one_apply] using this
  rw [Matrix.trace_fin_two, Λₗ_apply, Λₗ_apply, Matrix.det_fin_two, map_sub,
    cotOfEntry_apply, cotOfEntry_apply, cotOfEntry_apply, cotOfEntry_apply,
    toCotangent_δ_mul, toCotangent_δ_mul, map_sub, map_add, map_add, map_smul, map_smul,
    map_smul, map_smul, Algebra.smul_def, Algebra.smul_def, Algebra.smul_def, Algebra.smul_def,
    h00, h11, h01, h10, one_mul, one_mul, zero_mul, zero_mul, add_zero, sub_zero, add_comm]

theorem trace_Λₗ_eq_zero {M : Type} [CommRing M] [Algebra 𝒪 M]
    (φ : (RingHom.ker (x : B →+* 𝒪)).Cotangent →ₗ[𝒪] M)
    (τ : G) (hτ : Fbar x b G ρhom M τ = 1)
    (hdet : ∃ c, Matrix.det (LinearMap.toMatrix b b (ρhom τ)) = algebraMap 𝒪 B c) :
    Matrix.trace (Λₗ x b G ρhom φ τ) = 0 := by
  obtain ⟨c, hc⟩ := hdet
  rw [trace_Λₗ_eq_of_fbar_eq_one x b G ρhom φ τ hτ,
    show cotOfEntry x (Matrix.det (LinearMap.toMatrix b b (ρhom τ))) = 0 from ?_, map_zero]
  rw [cotOfEntry_apply, hc, δ_algebraMap, map_zero]

end MonoidHom

end LambdaDef

end WCOTTameD
p2m_reactivate "P2MW.S_GaloisRep_DeformationRingData_length_level_quotient_le_of_isUnramifiedAt.WCOTTameD"

open IsLocalRing TrivSqZeroExt

namespace WCOTTameD

variable (𝒪 : Type) [CommRing 𝒪] [IsDomain 𝒪] [IsDiscreteValuationRing 𝒪]
  (m : ℕ) [NeZero m]

abbrev Rm : Type := 𝒪 ⧸ (IsLocalRing.maximalIdeal 𝒪) ^ m

abbrev Am : Type := tsze (Rm 𝒪 m) (Rm 𝒪 m)

theorem maximalIdeal_pow_ne_top : (IsLocalRing.maximalIdeal 𝒪) ^ m ≠ ⊤ :=
  ne_of_lt (lt_of_le_of_lt (Ideal.pow_le_self (NeZero.ne m))
    (lt_top_iff_ne_top.mpr (IsLocalRing.maximalIdeal.isMaximal 𝒪).ne_top))

scoped instance : Nontrivial (Rm 𝒪 m) := Ideal.Quotient.nontrivial_iff.mpr (maximalIdeal_pow_ne_top 𝒪 m)

scoped instance : IsLocalRing (Rm 𝒪 m) :=
  .of_surjective' (Ideal.Quotient.mk _) Ideal.Quotient.mk_surjective

scoped instance : IsArtinianRing (Rm 𝒪 m) := by
  rw [isArtinianRing_iff_isNilpotent_maximalIdeal]
  refine ⟨m, ?_⟩
  rw [← map_maximalIdeal_of_surjective
        (Ideal.Quotient.mk ((IsLocalRing.maximalIdeal 𝒪) ^ m)) Ideal.Quotient.mk_surjective,
    ← Ideal.map_pow]
  simp

scoped instance : Nontrivial (Am 𝒪 m) := inl_injective.nontrivial

scoped instance : IsLocalRing (Am 𝒪 m) :=
  .of_isUnit_or_isUnit_one_sub_self fun a => by
    rw [isUnit_iff_isUnit_fst, isUnit_iff_isUnit_fst, fst_sub, fst_one]
    exact IsLocalRing.isUnit_or_isUnit_one_sub_self a.fst

noncomputable def amLinearEquivProd : Am 𝒪 m ≃ₗ[Rm 𝒪 m] Rm 𝒪 m × Rm 𝒪 m where
  toFun a := (a.fst, a.snd)
  invFun p := ⟨p.1, p.2⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

scoped instance : Module.Finite (Rm 𝒪 m) (Am 𝒪 m) :=
  Module.Finite.equiv (amLinearEquivProd 𝒪 m).symm

scoped instance : IsArtinianRing (Am 𝒪 m) :=
  IsArtinianRing.of_finite (Rm 𝒪 m) (Am 𝒪 m)

scoped instance : IsNoetherianRing (Am 𝒪 m) := inferInstance

scoped instance isAdicCompleteAm : IsAdicComplete (IsLocalRing.maximalIdeal (Am 𝒪 m)) (Am 𝒪 m) :=
  inferInstance

scoped instance : IsLocalHom (algebraMap 𝒪 (Rm 𝒪 m)) := by
  rw [Ideal.Quotient.algebraMap_eq]
  exact IsLocalHom.of_surjective _ Ideal.Quotient.mk_surjective

scoped instance isLocalHomAlgebraMapAm : IsLocalHom (algebraMap 𝒪 (Am 𝒪 m)) := by
  refine ⟨fun a ha => ?_⟩
  rw [show algebraMap 𝒪 (Am 𝒪 m) a = inl (algebraMap 𝒪 (Rm 𝒪 m) a) from rfl,
    isUnit_inl_iff] at ha
  exact (isUnit_map_iff (algebraMap 𝒪 (Rm 𝒪 m)) a).mp ha

theorem residue_surjective_Am :
    Function.Surjective (IsLocalRing.residue (Am 𝒪 m) ∘ algebraMap 𝒪 (Am 𝒪 m)) := by
  intro y
  obtain ⟨a, rfl⟩ := IsLocalRing.residue_surjective (R := Am 𝒪 m) y
  obtain ⟨a₀, ha₀⟩ := Ideal.Quotient.mk_surjective (I := (IsLocalRing.maximalIdeal 𝒪) ^ m) a.fst
  refine ⟨a₀, ?_⟩

  refine (Ideal.Quotient.mk_eq_mk_iff_sub_mem _ _).mpr ?_
  rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
  intro hu
  rw [isUnit_iff_isUnit_fst, fst_sub,
    show (algebraMap 𝒪 (Am 𝒪 m) a₀).fst = a.fst from by rw [← ha₀]; rfl, sub_self] at hu
  exact not_isUnit_zero hu

end WCOTTameD
p2m_reactivate "P2MW.S_GaloisRep_DeformationRingData_length_level_quotient_le_of_isUnramifiedAt.WCOTTameD"

open TrivSqZeroExt

namespace WCOTInvDict

variable {𝒪 B S : Type} [CommRing 𝒪] [CommRing B] [Algebra 𝒪 B] [CommRing S] [Algebra 𝒪 S]

noncomputable def sndOnKer (x : B →ₐ[𝒪] 𝒪) (ψ : B →ₐ[𝒪] tsze S S) :
    RingHom.ker (x : B →+* 𝒪) →ₗ[𝒪] S where
  toFun i := (ψ (i : B)).snd
  map_add' i j := by
    rw [Submodule.coe_add, map_add, snd_add]
  map_smul' c i := by
    simp only [Submodule.coe_smul_of_tower, map_smul, snd_smul, RingHom.id_apply]

theorem sndOnKer_apply (x : B →ₐ[𝒪] 𝒪) (ψ : B →ₐ[𝒪] tsze S S) (i : RingHom.ker (x : B →+* 𝒪)) :
    sndOnKer x ψ i = (ψ (i : B)).snd := rfl

theorem fst_eq_zero_of_mem (x : B →ₐ[𝒪] 𝒪) (ψ : B →ₐ[𝒪] tsze S S)
    (hψ : ∀ r : B, (ψ r).fst = algebraMap 𝒪 S (x r)) (i : RingHom.ker (x : B →+* 𝒪)) :
    (ψ (i : B)).fst = 0 := by
  have hi : x (i : B) = 0 := i.2
  rw [hψ, hi, map_zero]

noncomputable def derivOfLift (x : B →ₐ[𝒪] 𝒪) (ψ : B →ₐ[𝒪] tsze S S)
    (hψ : ∀ r : B, (ψ r).fst = algebraMap 𝒪 S (x r)) :
    (RingHom.ker (x : B →+* 𝒪)).Cotangent →ₗ[𝒪] S :=
  Ideal.Cotangent.lift (sndOnKer x ψ) fun i j => by
    rw [sndOnKer_apply, MulMemClass.coe_mul, map_mul, snd_mul, fst_eq_zero_of_mem x ψ hψ i,
      fst_eq_zero_of_mem x ψ hψ j, zero_smul, MulOpposite.op_zero, zero_smul, add_zero]

@[scoped simp] theorem derivOfLift_toCotangent (x : B →ₐ[𝒪] 𝒪) (ψ : B →ₐ[𝒪] tsze S S)
    (hψ : ∀ r : B, (ψ r).fst = algebraMap 𝒪 S (x r)) (i : RingHom.ker (x : B →+* 𝒪)) :
    derivOfLift x ψ hψ ((RingHom.ker (x : B →+* 𝒪)).toCotangent i) = (ψ (i : B)).snd :=
  Ideal.Cotangent.lift_toCotangent _ _ _

theorem sub_algebraMap_mem (x : B →ₐ[𝒪] 𝒪) (r : B) :
    r - algebraMap 𝒪 B (x r) ∈ RingHom.ker (x : B →+* 𝒪) := by
  rw [RingHom.mem_ker, map_sub]
  change x r - x (algebraMap 𝒪 B (x r)) = 0
  rw [AlgHom.commutes, Algebra.algebraMap_self_apply, sub_self]

theorem snd_eq_derivOfLift (x : B →ₐ[𝒪] 𝒪) (ψ : B →ₐ[𝒪] tsze S S)
    (hψ : ∀ r : B, (ψ r).fst = algebraMap 𝒪 S (x r)) (r : B) :
    (ψ r).snd = derivOfLift x ψ hψ
      ((RingHom.ker (x : B →+* 𝒪)).toCotangent ⟨r - algebraMap 𝒪 B (x r), sub_algebraMap_mem x r⟩) := by
  rw [derivOfLift_toCotangent, map_sub, snd_sub, AlgHom.commutes, algebraMap_eq_inl', snd_inl, sub_zero]

theorem ext_of_derivOfLift_eq (x : B →ₐ[𝒪] 𝒪) (ψ₁ ψ₂ : B →ₐ[𝒪] tsze S S)
    (h₁ : ∀ r : B, (ψ₁ r).fst = algebraMap 𝒪 S (x r)) (h₂ : ∀ r : B, (ψ₂ r).fst = algebraMap 𝒪 S (x r))
    (hD : derivOfLift x ψ₁ h₁ = derivOfLift x ψ₂ h₂) : ψ₁ = ψ₂ := by
  apply AlgHom.ext
  intro r
  apply TrivSqZeroExt.ext
  · rw [h₁, h₂]
  · rw [snd_eq_derivOfLift x ψ₁ h₁, snd_eq_derivOfLift x ψ₂ h₂, hD]

theorem derivOfLift_eq_zero_iff (x : B →ₐ[𝒪] 𝒪) (ψ : B →ₐ[𝒪] tsze S S)
    (hψ : ∀ r : B, (ψ r).fst = algebraMap 𝒪 S (x r)) :
    derivOfLift x ψ hψ = 0 ↔ ∀ r : B, (ψ r).snd = 0 := by
  constructor
  · intro h r
    rw [snd_eq_derivOfLift x ψ hψ, h, LinearMap.zero_apply]
  · intro h
    apply LinearMap.ext
    intro c
    obtain ⟨i, rfl⟩ := (RingHom.ker (x : B →+* 𝒪)).toCotangent_surjective c
    rw [derivOfLift_toCotangent, h, LinearMap.zero_apply]

end WCOTInvDict
p2m_reactivate "P2MW.S_GaloisRep_DeformationRingData_length_level_quotient_le_of_isUnramifiedAt.WCOTTameD P2MW.S_GaloisRep_DeformationRingData_length_level_quotient_le_of_isUnramifiedAt.WCOTInvDict"

open GaloisRep
open scoped TensorProduct

namespace WCOTXprime

section Naturality

variable {R S T : Type} [CommRing R] [CommRing S] [CommRing T] [Algebra R S] [Algebra S T]
  [Algebra R T] [IsScalarTower R S T]
  {V W : Type} [AddCommGroup V] [Module R V] [AddCommGroup W] [Module R W]

theorem cancel_naturality (φ : V →ₗ[R] W) (x : T ⊗[S] (S ⊗[R] V)) :
    TensorProduct.AlgebraTensorModule.cancelBaseChange R S T T W ((φ.baseChange S).baseChange T x) =
      φ.baseChange T (TensorProduct.AlgebraTensorModule.cancelBaseChange R S T T V x) := by
  induction x using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | tmul c y =>
    induction y using TensorProduct.induction_on with
    | zero => simp only [TensorProduct.tmul_zero, map_zero]
    | tmul b v =>
      simp only [LinearMap.baseChange_tmul, TensorProduct.AlgebraTensorModule.cancelBaseChange_tmul]
    | add y₁ y₂ h₁ h₂ => simp only [TensorProduct.tmul_add, map_add, h₁, h₂]
  | add x y hx hy => simp only [map_add, hx, hy]

end Naturality
p2m_reactivate "P2MW.S_GaloisRep_DeformationRingData_length_level_quotient_le_of_isUnramifiedAt.WCOTTameD P2MW.S_GaloisRep_DeformationRingData_length_level_quotient_le_of_isUnramifiedAt.WCOTInvDict"

variable {A B C : Type} [CommRing A] [IsLocalRing A] [CommRing B] [IsLocalRing B]
  [CommRing C] [IsLocalRing C]

noncomputable def bcComp (ρ : GaloisRepAdic A) (f : A →+* B) (hf : IsLocalHom f)
    (g : B →+* C) (hg : IsLocalHom g) (hgf : IsLocalHom (g.comp f)) :
    GaloisRepAdic.Equiv ((ρ.baseChangeAlong f hf).baseChangeAlong g hg)
      (ρ.baseChangeAlong (g.comp f) hgf) :=
  letI : Algebra A B := f.toAlgebra
  letI : Algebra B C := g.toAlgebra
  letI : Algebra A C := (g.comp f).toAlgebra
  haveI : IsScalarTower A B C := IsScalarTower.of_algebraMap_eq fun _ => rfl
  { toLinearEquiv := TensorProduct.AlgebraTensorModule.cancelBaseChange A B C C ρ.V
    map_apply := fun σ x => by
      change TensorProduct.AlgebraTensorModule.cancelBaseChange A B C C ρ.V
          ((((ρ.ρ σ).baseChange B).baseChange C) x) =
        ((ρ.ρ σ).baseChange C) (TensorProduct.AlgebraTensorModule.cancelBaseChange A B C C ρ.V x)
      exact cancel_naturality (ρ.ρ σ) x }

theorem isUnramifiedAt_of_isEquiv {ρ₁ ρ₂ : GaloisRepAdic A} (h : ρ₁.IsEquiv ρ₂) {q : ℕ}
    (hur : ρ₁.IsUnramifiedAt q) : ρ₂.IsUnramifiedAt q := by
  obtain ⟨e⟩ := h
  intro P hP τ hτ
  apply LinearMap.ext
  intro y
  obtain ⟨x, rfl⟩ := e.toLinearEquiv.surjective y
  rw [← e.map_apply, hur P hP τ hτ, Module.End.one_apply, Module.End.one_apply]

variable {𝒪 : Type} [CommRing 𝒪] [IsDomain 𝒪] [IsDiscreteValuationRing 𝒪]
  [IsAdicComplete (IsLocalRing.maximalIdeal 𝒪) 𝒪]
  {ρbar : ResidualGaloisRep (IsLocalRing.ResidueField 𝒪)}
  {𝒟₀ 𝒟' : ∀ ⦃A : Type⦄ [CommRing A] [IsLocalRing A] [Algebra 𝒪 A], GaloisRepAdic A → Prop}

theorem isEquiv_baseChangeAlong_comp
    (D₀ : DeformationRingData 𝒪 ρbar 𝒟₀) (D' : DeformationRingData 𝒪 ρbar 𝒟')
    (θ : D'.R →ₐ[𝒪] D₀.R) (hθ : IsLocalHom (θ : D'.R →+* D₀.R))
    (hθρ : (D'.ρ.baseChangeAlong (θ : D'.R →+* D₀.R) hθ).IsEquiv D₀.ρ)
    (x₀ : D₀.R →ₐ[𝒪] 𝒪) (hx₀ : IsLocalHom (x₀ : D₀.R →+* 𝒪))
    (hx' : IsLocalHom (x₀.comp θ : D'.R →+* 𝒪)) :
    (D'.ρ.baseChangeAlong (x₀.comp θ : D'.R →+* 𝒪) hx').IsEquiv
      (D₀.ρ.baseChangeAlong (x₀ : D₀.R →+* 𝒪) hx₀) := by
  obtain ⟨e⟩ := hθρ
  have hcomp : ((x₀ : D₀.R →+* 𝒪).comp (θ : D'.R →+* D₀.R)) = (x₀.comp θ : D'.R →+* 𝒪) :=
    RingHom.ext fun _ => rfl
  have hgf : IsLocalHom ((x₀ : D₀.R →+* 𝒪).comp (θ : D'.R →+* D₀.R)) := by rw [hcomp]; exact hx'
  have h1 : (D'.ρ.baseChangeAlong (x₀.comp θ : D'.R →+* 𝒪) hx').IsEquiv
      (D'.ρ.baseChangeAlong ((x₀ : D₀.R →+* 𝒪).comp (θ : D'.R →+* D₀.R)) hgf) := by
    have key : ∀ (f g : D'.R →+* 𝒪) (hf : IsLocalHom f) (hg : IsLocalHom g), f = g →
        (D'.ρ.baseChangeAlong f hf).IsEquiv (D'.ρ.baseChangeAlong g hg) := by
      intro f g hf hg hfg
      subst hfg
      exact ⟨GaloisRepAdic.Equiv.refl _⟩
    exact key _ _ hx' hgf hcomp.symm
  obtain ⟨e1⟩ := h1
  exact ⟨e1.trans ((bcComp D'.ρ (θ : D'.R →+* D₀.R) hθ (x₀ : D₀.R →+* 𝒪) hx₀ hgf).symm.trans
    (e.baseChangeAlong (x₀ : D₀.R →+* 𝒪) hx₀))⟩

theorem forall_inertia_apply_eq_one_comp
    (D₀ : DeformationRingData 𝒪 ρbar 𝒟₀) (D' : DeformationRingData 𝒪 ρbar 𝒟')
    (θ : D'.R →ₐ[𝒪] D₀.R) (hθ : IsLocalHom (θ : D'.R →+* D₀.R))
    (hθρ : (D'.ρ.baseChangeAlong (θ : D'.R →+* D₀.R) hθ).IsEquiv D₀.ρ)
    (x₀ : D₀.R →ₐ[𝒪] 𝒪) (hx₀ : IsLocalHom (x₀ : D₀.R →+* 𝒪))
    (hx' : IsLocalHom (x₀.comp θ : D'.R →+* 𝒪)) {q : ℕ}
    (hur : (D₀.ρ.baseChangeAlong (x₀ : D₀.R →+* 𝒪) hx₀).IsUnramifiedAt q) :
    ∀ P : ValuationSubring (AlgebraicClosure ℚ), P.LiesOverPrime q →
      ∀ τ ∈ P.inertiaSubgroupIn ℚ, (D'.ρ.baseChangeAlong (x₀.comp θ : D'.R →+* 𝒪) hx').ρ τ = 1 :=
  isUnramifiedAt_of_isEquiv
    ⟨(Classical.choice (isEquiv_baseChangeAlong_comp D₀ D' θ hθ hθρ x₀ hx₀ hx')).symm⟩ hur

end WCOTXprime
p2m_reactivate "P2MW.S_GaloisRep_DeformationRingData_length_level_quotient_le_of_isUnramifiedAt.WCOTTameD P2MW.S_GaloisRep_DeformationRingData_length_level_quotient_le_of_isUnramifiedAt.WCOTInvDict"

namespace WCOTTameD

open GaloisRep IsLocalRing TrivSqZeroExt

section xOfCotangentHom

variable {𝒪 : Type} [CommRing 𝒪] {B : Type} [CommRing B] [Algebra 𝒪 B]
  (x : B →ₐ[𝒪] 𝒪) {S : Type} [CommRing S] [Algebra 𝒪 S]

noncomputable def xOfCotangentHom (φ : (RingHom.ker (x : B →+* 𝒪)).Cotangent →ₗ[𝒪] S) :
    B →ₐ[𝒪] tsze S S where
  toFun r := ⟨algebraMap 𝒪 S (x r), φ (cotOfEntry x r)⟩
  map_one' := by ext <;> simp [cotOfEntry_apply, δ_one]
  map_mul' r s := by
    ext
    · simp only [fst_mk, fst_mul, map_mul]
    · simp only [snd_mk, snd_mul, fst_mk, cotOfEntry_apply, toCotangent_δ_mul, map_add, map_smul,
        Algebra.smul_def, op_smul_eq_smul, Algebra.algebraMap_self, RingHom.id_apply]
  map_zero' := by ext <;> simp
  map_add' r s := by ext <;> simp [cotOfEntry_apply, δ_add]
  commutes' c := by
    ext
    · show algebraMap 𝒪 S (x (algebraMap 𝒪 B c)) = (algebraMap 𝒪 (tsze S S) c).fst
      rw [x.commutes]; rfl
    · show φ (cotOfEntry x (algebraMap 𝒪 B c)) = (algebraMap 𝒪 (tsze S S) c).snd
      rw [cotOfEntry_apply, δ_algebraMap, map_zero, map_zero]; rfl

@[scoped simp] theorem fst_xOfCotangentHom (φ : (RingHom.ker (x : B →+* 𝒪)).Cotangent →ₗ[𝒪] S) (r : B) :
    (xOfCotangentHom x φ r).fst = algebraMap 𝒪 S (x r) := rfl

@[scoped simp] theorem snd_xOfCotangentHom (φ : (RingHom.ker (x : B →+* 𝒪)).Cotangent →ₗ[𝒪] S) (r : B) :
    (xOfCotangentHom x φ r).snd = φ (cotOfEntry x r) := rfl

theorem isLocalHom_xOfCotangentHom [IsLocalRing S] [IsLocalHom (algebraMap 𝒪 S)]
    [IsLocalRing (tsze S S)] [IsLocalHom (x : B →+* 𝒪)]
    (φ : (RingHom.ker (x : B →+* 𝒪)).Cotangent →ₗ[𝒪] S) :
    IsLocalHom (xOfCotangentHom x φ : B →+* tsze S S) := by
  refine ⟨fun r hr => ?_⟩
  rw [isUnit_iff_isUnit_fst] at hr
  exact (isUnit_map_iff (x : B →+* 𝒪) r).mp
    ((isUnit_map_iff (algebraMap 𝒪 S) (x r)).mp (fst_xOfCotangentHom x φ r ▸ hr))

end xOfCotangentHom
p2m_reactivate "P2MW.S_GaloisRep_DeformationRingData_length_level_quotient_le_of_isUnramifiedAt.WCOTTameD P2MW.S_GaloisRep_DeformationRingData_length_level_quotient_le_of_isUnramifiedAt.WCOTInvDict"

section hK

variable {𝒪 : Type} [CommRing 𝒪] [IsDomain 𝒪] [IsDiscreteValuationRing 𝒪]
  [IsAdicComplete (IsLocalRing.maximalIdeal 𝒪) 𝒪]
  {ρbar : ResidualGaloisRep (IsLocalRing.ResidueField 𝒪)}
  {𝒟₀ 𝒟' : ∀ ⦃A : Type⦄ [CommRing A] [IsLocalRing A] [Algebra 𝒪 A], GaloisRepAdic A → Prop}
  (D₀ : DeformationRingData 𝒪 ρbar 𝒟₀) (D' : DeformationRingData 𝒪 ρbar 𝒟')
  (θ : D'.R →ₐ[𝒪] D₀.R) (x₀ : D₀.R →ₐ[𝒪] 𝒪)
  (hx₀ : IsLocalHom (x₀ : D₀.R →+* 𝒪)) (hθ : IsLocalHom (θ : D'.R →+* D₀.R))

local notation "G_ℚ" => AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ

noncomputable abbrev xPrime : D'.R →ₐ[𝒪] 𝒪 := x₀.comp θ

noncomputable abbrev Φ' : Type := (RingHom.ker (xPrime D₀ D' θ x₀ : D'.R →+* 𝒪)).Cotangent

include hx₀ hθ in
theorem isLocalHom_xPrime : IsLocalHom (xPrime D₀ D' θ x₀ : D'.R →+* 𝒪) := by
  rw [show (xPrime D₀ D' θ x₀ : D'.R →+* 𝒪) = (x₀ : D₀.R →+* 𝒪).comp (θ : D'.R →+* D₀.R) from rfl]
  haveI := hθ; haveI := hx₀; exact RingHom.isLocalHom_comp _ _

noncomputable def bD : Module.Basis (Fin 2) D'.R D'.ρ.V :=
  Module.finBasisOfFinrankEq D'.R D'.ρ.V D'.ρ.finrank_eq

noncomputable def Λₗspec (m : ℕ) :
    (Φ' D₀ D' θ x₀ →ₗ[𝒪] Rm 𝒪 m) →ₗ[𝒪] ((G_ℚ) → Matrix (Fin 2) (Fin 2) (Rm 𝒪 m)) :=
  WCOTTameD.Λₗ (xPrime D₀ D' θ x₀) (bD D') (G_ℚ) (fun g => D'.ρ.ρ g)

noncomputable def Ksub (m : ℕ) : Submodule 𝒪 (Φ' D₀ D' θ x₀ →ₗ[𝒪] Rm 𝒪 m) :=
  LinearMap.range (LinearMap.lcomp 𝒪 (Rm 𝒪 m)
    (((Ideal.mapCotangent (RingHom.ker (xPrime D₀ D' θ x₀ : D'.R →ₐ[𝒪] 𝒪)) (RingHom.ker x₀) θ
      (fun _ hr => hr)).restrictScalars 𝒪)))

variable (m : ℕ) [NeZero m]

theorem baseChangeAlong_apply_eq_one_iff {A B' : Type} [CommRing A] [IsLocalRing A]
    [CommRing B'] [IsLocalRing B'] (f : A →+* B') (hf : IsLocalHom f)
    (ρ : GaloisRepAdic A) (b : Module.Basis (Fin 2) A ρ.V) (τ) :
    (ρ.baseChangeAlong f hf).ρ τ = 1 ↔ (LinearMap.toMatrix b b (ρ.ρ τ)).map f = 1 := by
  letI : Algebra A B' := f.toAlgebra
  have hM : LinearMap.toMatrix (b.baseChange B') (b.baseChange B')
      ((ρ.ρ τ).baseChange B') = (LinearMap.toMatrix b b (ρ.ρ τ)).map f := by
    ext i j
    simp only [LinearMap.toMatrix_apply, Matrix.map_apply, LinearMap.baseChange_tmul,
      Module.Basis.baseChange_apply, Module.Basis.baseChange_repr_tmul,
      RingHom.smul_toAlgebra, mul_one]
  have hrfl : (ρ.baseChangeAlong f hf).ρ τ = (ρ.ρ τ).baseChange B' := rfl
  constructor
  · intro h; rw [← hM, hrfl.symm.trans h]; exact LinearMap.toMatrix_one _
  · intro h; rw [hrfl]
    apply (LinearMap.toMatrix (b.baseChange B') (b.baseChange B')).injective
    rw [hM, h]; exact (LinearMap.toMatrix_one _).symm

theorem baseChangeAlong_xOfCotangentHom_apply_eq_one
    (φ : Φ' D₀ D' θ x₀ →ₗ[𝒪] Rm 𝒪 m)
    (τ : G_ℚ)
    (hurτ : (D'.ρ.baseChangeAlong (xPrime D₀ D' θ x₀ : D'.R →+* 𝒪)
      (isLocalHom_xPrime D₀ D' θ x₀ hx₀ hθ)).ρ τ = 1)
    (hΛ0τ : Λₗspec D₀ D' θ x₀ m φ τ = 0) :
    haveI := isLocalHom_xPrime D₀ D' θ x₀ hx₀ hθ
    (D'.ρ.baseChangeAlong (xOfCotangentHom (xPrime D₀ D' θ x₀) φ : D'.R →+* Am 𝒪 m)
      (isLocalHom_xOfCotangentHom (xPrime D₀ D' θ x₀) φ)).ρ τ = 1 := by
  set x' := (xPrime D₀ D' θ x₀ : D'.R →+* 𝒪)
  set M := LinearMap.toMatrix (bD D') (bD D') (D'.ρ.ρ τ)
  have hur' : M.map x' = 1 :=
    (baseChangeAlong_apply_eq_one_iff x' (isLocalHom_xPrime D₀ D' θ x₀ hx₀ hθ) D'.ρ (bD D') τ).mp
      hurτ
  haveI := isLocalHom_xPrime D₀ D' θ x₀ hx₀ hθ
  rw [baseChangeAlong_apply_eq_one_iff _ _ D'.ρ (bD D') τ]
  show M.map (xOfCotangentHom (xPrime D₀ D' θ x₀) φ : D'.R →+* Am 𝒪 m) = 1
  refine Matrix.ext fun i j => ?_
  have hfst : x' (M i j) = (1 : Matrix (Fin 2) (Fin 2) 𝒪) i j := by
    have := congrFun (congrFun hur' i) j; rwa [Matrix.map_apply] at this
  have hsnd : φ (cotOfEntry (xPrime D₀ D' θ x₀) (M i j)) = 0 := by
    have := congrFun (congrFun hΛ0τ i) j
    simpa only [Λₗspec, Λₗ_apply, Matrix.zero_apply] using this
  rw [Matrix.map_apply]
  refine TrivSqZeroExt.ext ?_ ?_
  · show algebraMap 𝒪 (Rm 𝒪 m) (x' (M i j)) = ((1 : Matrix (Fin 2) (Fin 2) (Am 𝒪 m)) i j).fst
    rw [hfst, Matrix.one_apply, Matrix.one_apply]
    split <;> simp
  · show φ (cotOfEntry (xPrime D₀ D' θ x₀) (M i j))
      = ((1 : Matrix (Fin 2) (Fin 2) (Am 𝒪 m)) i j).snd
    rw [hsnd, Matrix.one_apply]
    split <;> simp

include hx₀ hθ in

theorem Λₗ_hK (q : ℕ) (hθρ : (D'.ρ.baseChangeAlong (θ : D'.R →+* D₀.R) hθ).IsEquiv D₀.ρ)
    (hθsurj : Function.Surjective (θ : D'.R →+* D₀.R))
    (hur : ∀ P' : ValuationSubring (AlgebraicClosure ℚ), P'.LiesOverPrime q →
      ∀ τ ∈ P'.inertiaSubgroupIn ℚ,
        (D'.ρ.baseChangeAlong (xPrime D₀ D' θ x₀ : D'.R →+* 𝒪)
          (isLocalHom_xPrime D₀ D' θ x₀ hx₀ hθ)).ρ τ = 1)
    (H1 : ∀ {A : Type} [CommRing A] [IsLocalRing A] [Algebra 𝒪 A] (ρA : GaloisRepAdic A),
      ∀ {B : Type} [CommRing B] [IsLocalRing B] [Algebra 𝒪 B] (f : A →+* B) (hf : IsLocalHom f),
        𝒟' ρA → 𝒟' (ρA.baseChangeAlong f hf))
    (H2 : ∀ {A : Type} [CommRing A] [IsLocalRing A] [Algebra 𝒪 A] (ρA : GaloisRepAdic A),
      𝒟' ρA → (∀ P' : ValuationSubring (AlgebraicClosure ℚ), P'.LiesOverPrime q →
        ∀ τ ∈ P'.inertiaSubgroupIn ℚ, ρA.ρ τ = 1) → 𝒟₀ ρA)
    (φ : Φ' D₀ D' θ x₀ →ₗ[𝒪] Rm 𝒪 m)
    (hΛ0 : ∀ P' : ValuationSubring (AlgebraicClosure ℚ), P'.LiesOverPrime q →
      ∀ τ ∈ P'.inertiaSubgroupIn ℚ, Λₗspec D₀ D' θ x₀ m φ τ = 0) :
    φ ∈ Ksub D₀ D' θ x₀ m := by
  haveI hx' := isLocalHom_xPrime D₀ D' θ x₀ hx₀ hθ

  set xφ := xOfCotangentHom (xPrime D₀ D' θ x₀) (S := Rm 𝒪 m) φ with hxφdef
  have hxφ : IsLocalHom (xφ : D'.R →+* Am 𝒪 m) :=
    isLocalHom_xOfCotangentHom (xPrime D₀ D' θ x₀) φ

  have h𝒟' : 𝒟' (D'.ρ.baseChangeAlong (xφ : D'.R →+* Am 𝒪 m) hxφ) :=
    H1 D'.ρ (xφ : D'.R →+* Am 𝒪 m) hxφ D'.isOfType

  have hurφ : ∀ P' : ValuationSubring (AlgebraicClosure ℚ), P'.LiesOverPrime q →
      ∀ τ ∈ P'.inertiaSubgroupIn ℚ,
        (D'.ρ.baseChangeAlong (xφ : D'.R →+* Am 𝒪 m) hxφ).ρ τ = 1 :=
    fun P' hP' τ hτ => baseChangeAlong_xOfCotangentHom_apply_eq_one D₀ D' θ x₀ hx₀ hθ m φ τ
      (hur P' hP' τ hτ) (hΛ0 P' hP' τ hτ)

  have h𝒟₀ : 𝒟₀ (D'.ρ.baseChangeAlong (xφ : D'.R →+* Am 𝒪 m) hxφ) := H2 _ h𝒟' hurφ

  obtain ⟨ψ, hψloc, hψθ⟩ := GaloisRep.DeformationRingData.exists_algHom_comp_eq_of_isOfType D₀ D' θ hθ hθρ (Am 𝒪 m)
    (residue_surjective_Am 𝒪 m) xφ hxφ h𝒟' h𝒟₀

  have hψfst : ∀ r : D₀.R, (ψ r).fst = algebraMap 𝒪 (Rm 𝒪 m) (x₀ r) := fun r => by
    obtain ⟨s, rfl⟩ := hθsurj r
    show ((ψ.comp θ) s).fst = _
    rw [hψθ, hxφdef, fst_xOfCotangentHom]; rfl

  refine ⟨WCOTInvDict.derivOfLift x₀ ψ hψfst, ?_⟩

  apply LinearMap.ext
  intro c
  obtain ⟨i', rfl⟩ := Ideal.toCotangent_surjective _ c
  rw [LinearMap.lcomp_apply', LinearMap.comp_apply]
  show WCOTInvDict.derivOfLift x₀ ψ hψfst
      ((Ideal.mapCotangent _ _ θ _) ((RingHom.ker _).toCotangent i'))
    = φ ((RingHom.ker _).toCotangent i')
  rw [Ideal.mapCotangent_toCotangent, WCOTInvDict.derivOfLift_toCotangent]
  show ((ψ.comp θ) (i' : D'.R)).snd = _
  rw [hψθ, hxφdef, snd_xOfCotangentHom, cotOfEntry_apply]
  congr 1
  refine congrArg _ (Subtype.ext ?_)
  show ((i' : D'.R) - algebraMap 𝒪 D'.R ((xPrime D₀ D' θ x₀ : D'.R →+* 𝒪) i') : D'.R) = i'
  rw [show (xPrime D₀ D' θ x₀ : D'.R →+* 𝒪) (i' : D'.R) = 0 from i'.2, map_zero, sub_zero]

end hK
p2m_reactivate "P2MW.S_GaloisRep_DeformationRingData_length_level_quotient_le_of_isUnramifiedAt.WCOTTameD P2MW.S_GaloisRep_DeformationRingData_length_level_quotient_le_of_isUnramifiedAt.WCOTInvDict"

end WCOTTameD
p2m_reactivate "P2MW.S_GaloisRep_DeformationRingData_length_level_quotient_le_of_isUnramifiedAt.WCOTTameD P2MW.S_GaloisRep_DeformationRingData_length_level_quotient_le_of_isUnramifiedAt.WCOTInvDict"

open Polynomial

namespace WCOTFglue

theorem trace_and_det_of_charpoly_eq {R : Type} [CommRing R] [Nontrivial R]
    (M : Matrix (Fin 2) (Fin 2) R) (a q : R)
    (hch : M.charpoly = X ^ 2 - C a * X + C q) :
    M.trace = a ∧ M.det = q := by
  have key : X ^ 2 - C M.trace * X + C M.det = (X ^ 2 - C a * X + C q : R[X]) :=
    (Matrix.charpoly_fin_two M).symm.trans hch
  have keyD : C M.det - C M.trace * X = (C q - C a * X : R[X]) := by
    have := key; ring_nf at this ⊢; linear_combination this
  constructor
  · have h1 := congrArg (fun p => Polynomial.coeff p 1) keyD
    simp only [Polynomial.coeff_sub, Polynomial.coeff_C, Polynomial.coeff_mul_X] at h1
    simpa [show (1 : ℕ) ≠ 0 from one_ne_zero] using h1
  · have h0 := congrArg (fun p => Polynomial.coeff p 0) keyD
    simp only [Polynomial.coeff_sub, Polynomial.coeff_C] at h0
    simpa using h0

variable {B 𝒪 : Type} [CommRing B] [IsLocalRing B] [CommRing 𝒪] [IsLocalRing 𝒪]

omit [IsLocalRing 𝒪] in

theorem toMatrix_map_mul_toMatrix_map_inv (ρ : GaloisRepAdic B) (x : B →+* 𝒪)
    (b : Module.Basis (Fin 2) B ρ.V) (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) :
    (LinearMap.toMatrix b b (ρ.ρ σ)).map x * (LinearMap.toMatrix b b (ρ.ρ σ⁻¹)).map x = 1 := by
  rw [← Matrix.map_mul, ← LinearMap.toMatrix_mul, ← map_mul, mul_inv_cancel, map_one, LinearMap.toMatrix_one]
  exact Matrix.map_one x (map_zero x) (map_one x)

theorem charpoly_toMatrix_map (ρ : GaloisRepAdic B) (x : B →+* 𝒪) (hx : IsLocalHom x)
    (b : Module.Basis (Fin 2) B ρ.V) (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) :
    ((LinearMap.toMatrix b b (ρ.ρ σ)).map x).charpoly = LinearMap.charpoly ((ρ.baseChangeAlong x hx).ρ σ) := by
  letI : Algebra B 𝒪 := x.toAlgebra
  rw [Matrix.charpoly_map, LinearMap.charpoly_toMatrix]
  show (LinearMap.charpoly (ρ.ρ σ)).map x = LinearMap.charpoly ((ρ.ρ σ).baseChange 𝒪)
  rw [LinearMap.charpoly_baseChange]
  rfl

theorem trace_and_det_of_charpoly_fibre [Nontrivial 𝒪] (ρ : GaloisRepAdic B) (x : B →+* 𝒪) (hx : IsLocalHom x)
    (b : Module.Basis (Fin 2) B ρ.V) (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (a c : 𝒪)
    (hchar : LinearMap.charpoly ((ρ.baseChangeAlong x hx).ρ σ) = X ^ 2 - C a * X + C c) :
    ((LinearMap.toMatrix b b (ρ.ρ σ)).map x).trace = a ∧ ((LinearMap.toMatrix b b (ρ.ρ σ)).map x).det = c :=
  trace_and_det_of_charpoly_eq _ a c ((charpoly_toMatrix_map ρ x hx b σ).trans hchar)

theorem charpoly_eq_of_isEquiv {A : Type} [CommRing A] [IsLocalRing A] {ρ₁ ρ₂ : GaloisRepAdic A}
    (h : ρ₁.IsEquiv ρ₂) (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) :
    LinearMap.charpoly (ρ₁.ρ σ) = LinearMap.charpoly (ρ₂.ρ σ) := by
  obtain ⟨e⟩ := h
  have hconj : e.toLinearEquiv.conj (ρ₁.ρ σ) = ρ₂.ρ σ := by
    apply LinearMap.ext
    intro y
    rw [LinearEquiv.conj_apply_apply, e.map_apply, LinearEquiv.apply_symm_apply]
  rw [← hconj, LinearEquiv.charpoly_conj]

end WCOTFglue
p2m_reactivate "P2MW.S_GaloisRep_DeformationRingData_length_level_quotient_le_of_isUnramifiedAt.WCOTTameD P2MW.S_GaloisRep_DeformationRingData_length_level_quotient_le_of_isUnramifiedAt.WCOTInvDict"

namespace WCOTFinal

open WCOTTameD

variable {𝒪 : Type} [CommRing 𝒪] [IsDomain 𝒪] [IsDiscreteValuationRing 𝒪]
  [IsAdicComplete (IsLocalRing.maximalIdeal 𝒪) 𝒪]
  {ρbar : ResidualGaloisRep (IsLocalRing.ResidueField 𝒪)}
  {𝒟₀ 𝒟' : ∀ ⦃A : Type⦄ [CommRing A] [IsLocalRing A] [Algebra 𝒪 A], GaloisRepAdic A → Prop}
  (D₀ : DeformationRingData 𝒪 ρbar 𝒟₀) (D' : DeformationRingData 𝒪 ρbar 𝒟')
  (θ : D'.R →ₐ[𝒪] D₀.R) (x₀ : D₀.R →ₐ[𝒪] 𝒪)

set_option maxSynthPendingDepth 3 in

theorem ksub_le_ker_lcomp (m : ℕ) :
    Ksub D₀ D' θ x₀ m ≤ LinearMap.ker (LinearMap.lcomp 𝒪 (Rm 𝒪 m)
      (COT1.cotangentRelaxKer D₀ D' θ x₀).subtype) := by
  rintro φ ⟨φ₀, rfl⟩
  have h : LinearMap.lcomp 𝒪 (Rm 𝒪 m) (COT1.cotangentRelaxKer D₀ D' θ x₀).subtype
      ((LinearMap.lcomp 𝒪 (Rm 𝒪 m)
        (((RingHom.ker (xPrime D₀ D' θ x₀ : D'.R →ₐ[𝒪] 𝒪)).mapCotangent (RingHom.ker x₀) θ
          (fun _ hr => hr)).restrictScalars 𝒪)) φ₀) = 0 := by
    ext k
    have hk0 : ((RingHom.ker (xPrime D₀ D' θ x₀ : D'.R →ₐ[𝒪] 𝒪)).mapCotangent (RingHom.ker x₀) θ
        (fun _ hr => hr)) k.1 = 0 := LinearMap.mem_ker.mp k.2
    show φ₀ (((RingHom.ker (xPrime D₀ D' θ x₀ : D'.R →ₐ[𝒪] 𝒪)).mapCotangent (RingHom.ker x₀) θ
      (fun _ hr => hr)) k.1) = 0
    rw [hk0]
    exact map_zero φ₀
  exact (LinearMap.mem_ker (f := LinearMap.lcomp 𝒪 (Rm 𝒪 m)
    (COT1.cotangentRelaxKer D₀ D' θ x₀).subtype)).mpr h

end WCOTFinal
p2m_reactivate "P2MW.S_GaloisRep_DeformationRingData_length_level_quotient_le_of_isUnramifiedAt.WCOTTameD P2MW.S_GaloisRep_DeformationRingData_length_level_quotient_le_of_isUnramifiedAt.WCOTInvDict"

section RowTwelve

open WCOTTameD WCOTFinal

theorem solution
    {𝒪 : Type} [CommRing 𝒪] [IsDomain 𝒪] [IsDiscreteValuationRing 𝒪]
    [IsAdicComplete (IsLocalRing.maximalIdeal 𝒪) 𝒪]
    {ρbar : ResidualGaloisRep (IsLocalRing.ResidueField 𝒪)}
    {𝒟₀ 𝒟' : ∀ ⦃A : Type⦄ [CommRing A] [IsLocalRing A] [Algebra 𝒪 A], GaloisRepAdic A → Prop}
    (D₀ : GaloisRep.DeformationRingData 𝒪 ρbar 𝒟₀) (D' : GaloisRep.DeformationRingData 𝒪 ρbar 𝒟')
    (θ : D'.R →ₐ[𝒪] D₀.R) (x₀ : D₀.R →ₐ[𝒪] 𝒪)
    (p q : ℕ) (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q)
    (hp𝔪 : (p : 𝒪) ∈ IsLocalRing.maximalIdeal 𝒪)
    (hθ : IsLocalHom (θ : D'.R →+* D₀.R)) (hx₀ : IsLocalHom (x₀ : D₀.R →+* 𝒪))
    (hθρ : (D'.ρ.baseChangeAlong (θ : D'.R →+* D₀.R) hθ).IsEquiv D₀.ρ)
    (hθsurj : Function.Surjective θ)
    (P : ValuationSubring (AlgebraicClosure ℚ)) (hP : P.LiesOverPrime q)
    (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (hσ : P.IsFrobeniusAt σ q)
    (hconj : ∀ P' : ValuationSubring (AlgebraicClosure ℚ), P'.LiesOverPrime q →
      ∃ g : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ, g • P = P')
    (a : 𝒪)
    (hchar : (LinearMap.charpoly ((D₀.ρ.baseChangeAlong (x₀ : D₀.R →+* 𝒪) hx₀).ρ σ)) =
      Polynomial.X ^ 2 - Polynomial.C a * Polynomial.X + Polynomial.C ((q : 𝒪)))
    (hur : (D₀.ρ.baseChangeAlong (x₀ : D₀.R →+* 𝒪) hx₀).IsUnramifiedAt q)
    (Hdet : ∀ {A : Type} [CommRing A] [IsLocalRing A] [Algebra 𝒪 A] (ρA : GaloisRepAdic A),
      𝒟' ρA → ρA.DetIsCyclotomic p)
    (H1 : ∀ {A : Type} [CommRing A] [IsLocalRing A] [Algebra 𝒪 A] (ρA : GaloisRepAdic A)
        {B : Type} [CommRing B] [IsLocalRing B] [Algebra 𝒪 B] (f : A →+* B) (hf : IsLocalHom f),
      𝒟' ρA → 𝒟' (ρA.baseChangeAlong f hf))
    (H2 : ∀ {A : Type} [CommRing A] [IsLocalRing A] [Algebra 𝒪 A] (ρA : GaloisRepAdic A),
      𝒟' ρA → (∀ P' : ValuationSubring (AlgebraicClosure ℚ), P'.LiesOverPrime q →
        ∀ τ ∈ P'.inertiaSubgroupIn ℚ, ρA.ρ τ = 1) → 𝒟₀ ρA)
    (hdivI : ∀ (k : ℕ) (τ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ), τ ∈ P.inertiaSubgroupIn ℚ →
      ∃ w : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ, w ∈ P.inertiaSubgroupIn ℚ ∧
        w ^ (p ^ k) = σ * τ * σ⁻¹ * (τ ^ q)⁻¹)
    (hgen : ∀ m : ℕ, ∃ γ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ, γ ∈ P.inertiaSubgroupIn ℚ ∧
      ∀ τ ∈ P.inertiaSubgroupIn ℚ, ∃ (j : ℕ) (x w : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ),
        x ∈ P.inertiaSubgroupIn ℚ ∧ w ∈ P.inertiaSubgroupIn ℚ ∧ τ = γ ^ j * x ^ (p ^ m) * w ^ (p ^ m))
    (n : ℕ) :
    Module.length 𝒪 (((RingHom.ker (x₀.comp θ : D'.R →ₐ[𝒪] 𝒪)).Cotangent →ₗ[𝒪]
        𝒪 ⧸ (IsLocalRing.maximalIdeal 𝒪) ^ (n + 1)) ⧸
      LinearMap.ker (LinearMap.lcomp 𝒪 (𝒪 ⧸ (IsLocalRing.maximalIdeal 𝒪) ^ (n + 1))
        (LinearMap.ker (Ideal.mapCotangent (RingHom.ker (x₀.comp θ : D'.R →ₐ[𝒪] 𝒪))
            (RingHom.ker x₀) θ (fun _ hr => hr))).subtype)) ≤
    Module.length 𝒪 (𝒪 ⧸ Ideal.span {((q : 𝒪) - 1) * (a ^ 2 - ((q : 𝒪) + 1) ^ 2)}) := by
  classical
  have _ := hσ
  have hdetD' : D'.ρ.DetIsCyclotomic p := Hdet D'.ρ D'.isOfType
  have hx' : IsLocalHom (xPrime D₀ D' θ x₀ : D'.R →+* 𝒪) :=
    isLocalHom_xPrime D₀ D' θ x₀ hx₀ hθ
  have hθsurj' : Function.Surjective (θ : D'.R →+* D₀.R) := hθsurj
  have hiso := WCOTXprime.isEquiv_baseChangeAlong_comp D₀ D' θ hθ hθρ x₀ hx₀ hx'
  have hchar' : LinearMap.charpoly
      ((D'.ρ.baseChangeAlong (xPrime D₀ D' θ x₀ : D'.R →+* 𝒪) hx').ρ σ) =
      Polynomial.X ^ 2 - Polynomial.C a * Polynomial.X + Polynomial.C ((q : 𝒪)) :=
    (WCOTFglue.charpoly_eq_of_isEquiv hiso σ).trans hchar
  obtain ⟨htrF, hdetF⟩ := WCOTFglue.trace_and_det_of_charpoly_fibre D'.ρ
    (xPrime D₀ D' θ x₀ : D'.R →+* 𝒪) hx' (bD D') σ a ((q : 𝒪)) hchar'
  have hur' := WCOTXprime.forall_inertia_apply_eq_one_comp D₀ D' θ hθ hθρ x₀ hx₀ hx' hur
  have hFbar1 : ∀ (m : ℕ) (τ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ),
      τ ∈ P.inertiaSubgroupIn ℚ →
      Fbar (xPrime D₀ D' θ x₀) (bD D') (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)
        (fun g => D'.ρ.ρ g) (Rm 𝒪 (m + 1)) τ = 1 := by
    intro m τ hτ
    have h1 := (baseChangeAlong_apply_eq_one_iff (xPrime D₀ D' θ x₀ : D'.R →+* 𝒪) hx'
      D'.ρ (bD D') τ).mp (hur' P hP τ hτ)
    show (LinearMap.toMatrix (bD D') (bD D') (D'.ρ.ρ τ)).map
        ((algebraMap 𝒪 (Rm 𝒪 (m + 1))).comp (xPrime D₀ D' θ x₀ : D'.R →+* 𝒪)) = 1
    rw [RingHom.coe_comp, ← Matrix.map_map, h1]
    exact Matrix.map_one _ (map_zero _) (map_one _)
  have hFbar_eq : ∀ (m : ℕ) (g : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ),
      Fbar (xPrime D₀ D' θ x₀) (bD D') (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)
        (fun g => D'.ρ.ρ g) (Rm 𝒪 (m + 1)) g =
      ((LinearMap.toMatrix (bD D') (bD D') (D'.ρ.ρ g)).map
        (xPrime D₀ D' θ x₀ : D'.R →+* 𝒪)).map
          (Ideal.Quotient.mk ((IsLocalRing.maximalIdeal 𝒪) ^ (m + 1))) := by
    intro m g
    show (LinearMap.toMatrix (bD D') (bD D') (D'.ρ.ρ g)).map
        ((algebraMap 𝒪 (Rm 𝒪 (m + 1))).comp (xPrime D₀ D' θ x₀ : D'.R →+* 𝒪)) = _
    rw [RingHom.coe_comp, ← Matrix.map_map, Ideal.Quotient.algebraMap_eq]
  have hdet1 : ∀ τ ∈ P.inertiaSubgroupIn ℚ, ∃ c : 𝒪,
      Matrix.det (LinearMap.toMatrix (bD D') (bD D') (D'.ρ.ρ τ)) = algebraMap 𝒪 D'.R c :=
    fun τ hτ => ⟨1, by
      rw [map_one, LinearMap.det_toMatrix]
      exact GaloisRepAdic.det_eq_one_of_mem_inertiaSubgroupIn D'.ρ hp hq hpq hdetD' P hP τ hτ⟩
  have hadd : ∀ (m : ℕ) (φ : (RingHom.ker (x₀.comp θ : D'.R →ₐ[𝒪] 𝒪)).Cotangent →ₗ[𝒪]
      𝒪 ⧸ (IsLocalRing.maximalIdeal 𝒪) ^ (m + 1)),
      ∀ x ∈ P.inertiaSubgroupIn ℚ, ∀ y ∈ P.inertiaSubgroupIn ℚ,
      Λₗspec D₀ D' θ x₀ (m + 1) φ (x * y) =
        Λₗspec D₀ D' θ x₀ (m + 1) φ x + Λₗspec D₀ D' θ x₀ (m + 1) φ y := by
    intro m φ x hx y hy
    exact Λₗ_hadd' (xPrime D₀ D' θ x₀) (bD D') _ (D'.ρ.ρ) φ x y
      (hFbar1 m x hx) (hFbar1 m y hy)
  have hequiv : ∀ (m : ℕ) (φ : (RingHom.ker (x₀.comp θ : D'.R →ₐ[𝒪] 𝒪)).Cotangent →ₗ[𝒪]
      𝒪 ⧸ (IsLocalRing.maximalIdeal 𝒪) ^ (m + 1)),
      ∀ τ ∈ P.inertiaSubgroupIn ℚ,
      Λₗspec D₀ D' θ x₀ (m + 1) φ (σ * τ * σ⁻¹) =
        ((LinearMap.toMatrix (bD D') (bD D') (D'.ρ.ρ σ)).map
          (xPrime D₀ D' θ x₀ : D'.R →+* 𝒪)).map
            (Ideal.Quotient.mk ((IsLocalRing.maximalIdeal 𝒪) ^ (m + 1))) *
          Λₗspec D₀ D' θ x₀ (m + 1) φ τ *
        ((LinearMap.toMatrix (bD D') (bD D') (D'.ρ.ρ σ⁻¹)).map
          (xPrime D₀ D' θ x₀ : D'.R →+* 𝒪)).map
            (Ideal.Quotient.mk ((IsLocalRing.maximalIdeal 𝒪) ^ (m + 1))) := by
    intro m φ τ hτ
    rw [← hFbar_eq m σ, ← hFbar_eq m σ⁻¹]
    exact Λₗ_conj_of_fbar_eq_one (xPrime D₀ D' θ x₀) (bD D') _ (D'.ρ.ρ) φ σ τ
      (hFbar1 m τ hτ)
  have hΛconj : ∀ (m : ℕ) (φ : (RingHom.ker (x₀.comp θ : D'.R →ₐ[𝒪] 𝒪)).Cotangent →ₗ[𝒪]
      𝒪 ⧸ (IsLocalRing.maximalIdeal 𝒪) ^ (m + 1))
      (g τ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ),
      τ ∈ P.inertiaSubgroupIn ℚ → Λₗspec D₀ D' θ x₀ (m + 1) φ τ = 0 →
      Λₗspec D₀ D' θ x₀ (m + 1) φ (g * τ * g⁻¹) = 0 := by
    intro m φ g τ hτ h0
    exact Λₗ_conj_eq_zero (xPrime D₀ D' θ x₀) (bD D') _ (D'.ρ.ρ) φ g τ
      (hFbar1 m τ hτ) h0
  have htr0 : ∀ (m : ℕ) (φ : (RingHom.ker (x₀.comp θ : D'.R →ₐ[𝒪] 𝒪)).Cotangent →ₗ[𝒪]
      𝒪 ⧸ (IsLocalRing.maximalIdeal 𝒪) ^ (m + 1)),
      ∀ τ ∈ P.inertiaSubgroupIn ℚ, Matrix.trace (Λₗspec D₀ D' θ x₀ (m + 1) φ τ) = 0 := by
    intro m φ τ hτ
    exact trace_Λₗ_eq_zero (xPrime D₀ D' θ x₀) (bD D') _ (D'.ρ.ρ) φ τ
      (hFbar1 m τ hτ) (hdet1 τ hτ)
  have hKplug : ∀ (m : ℕ) (φ : (RingHom.ker (x₀.comp θ : D'.R →ₐ[𝒪] 𝒪)).Cotangent →ₗ[𝒪]
      𝒪 ⧸ (IsLocalRing.maximalIdeal 𝒪) ^ (m + 1)),
      (∀ P' : ValuationSubring (AlgebraicClosure ℚ), P'.LiesOverPrime q →
        ∀ τ ∈ P'.inertiaSubgroupIn ℚ, Λₗspec D₀ D' θ x₀ (m + 1) φ τ = 0) →
      φ ∈ LinearMap.ker (LinearMap.lcomp 𝒪 (𝒪 ⧸ (IsLocalRing.maximalIdeal 𝒪) ^ (m + 1))
        (COT1.cotangentRelaxKer D₀ D' θ x₀).subtype) := by
    intro m φ h0
    exact ksub_le_ker_lcomp D₀ D' θ x₀ (m + 1)
      (Λₗ_hK (q := q) (hθ := hθ) (hx₀ := hx₀) (hθρ := hθρ) (hθsurj := hθsurj')
        (hur := hur') (H1 := @H1) (H2 := @H2) (φ := φ) (hΛ0 := h0))
  obtain ⟨γ, hγI, hgenn⟩ := hgen (n + 1)
  exact Module.length_quotient_le_of_inertia_additive_family (P.inertiaSubgroupIn ℚ) σ γ hγI
    p q (n + 1) hp𝔪 (fun τ hτ => hdivI (n + 1) τ hτ) hgenn
    ((LinearMap.toMatrix (bD D') (bD D') (D'.ρ.ρ σ)).map (xPrime D₀ D' θ x₀ : D'.R →+* 𝒪))
    ((LinearMap.toMatrix (bD D') (bD D') (D'.ρ.ρ σ⁻¹)).map (xPrime D₀ D' θ x₀ : D'.R →+* 𝒪))
    (WCOTFglue.toMatrix_map_mul_toMatrix_map_inv D'.ρ (xPrime D₀ D' θ x₀ : D'.R →+* 𝒪)
      (bD D') σ)
    a htrF hdetF
    (WCOTTameQbar.isUnit_natCast_of_coprime_of_mem ((Nat.coprime_primes hp hq).mpr hpq) hp𝔪)
    (Λₗspec D₀ D' θ x₀ (n + 1)) (hadd n) (hequiv n) (htr0 n) _
    (fun φ h0 => hKplug n φ (WCOTInertiaConj.forall_inertia_eq_zero_of_conj P hconj
      (Λₗspec D₀ D' θ x₀ (n + 1) φ) (hΛconj n φ) h0))

end RowTwelve
p2m_reactivate "P2MW.S_GaloisRep_DeformationRingData_length_level_quotient_le_of_isUnramifiedAt.WCOTTameD P2MW.S_GaloisRep_DeformationRingData_length_level_quotient_le_of_isUnramifiedAt.WCOTInvDict"

end S_GaloisRep_DeformationRingData_length_level_quotient_le_of_isUnramifiedAt
end P2MW
export P2MW.S_GaloisRep_DeformationRingData_length_level_quotient_le_of_isUnramifiedAt (solution)
