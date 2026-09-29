-- Prove2me | solution 1 for GaloisRep.DeformationRingData.length_level_quotient_le_of_isUnipotentOnInertiaAt
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:07.331093+00:00
-- url     : https://prove2.me/submissions/31e0be1d-25d9-5c22-a231-1dbc85121a66

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
import Definitions.Def_FLTPrelim_Ramification
import Mathlib.Algebra.Ring.GeomSum
import Mathlib.Algebra.TrivSqZeroExt.Basic
import Mathlib.LinearAlgebra.Charpoly.ToMatrix
import Mathlib.LinearAlgebra.Determinant
import Mathlib.LinearAlgebra.Matrix.Charpoly.Basic
import Mathlib.LinearAlgebra.Matrix.Charpoly.Coeff
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.RingTheory.AdicCompletion.Noetherian
import Mathlib.RingTheory.Artinian.Module
import Mathlib.RingTheory.Coprime.Lemmas
import Mathlib.RingTheory.Filtration
import Mathlib.RingTheory.Finiteness.Prod
import Mathlib.RingTheory.HopkinsLevitzki
import Mathlib.RingTheory.Ideal.Quotient.Noetherian
import Mathlib.RingTheory.LocalRing.Quotient
import Mathlib.RingTheory.LocalRing.ResidueField.Basic
import Mathlib.RingTheory.PrincipalIdealDomain
import Mathlib.Tactic.Group
import Mathlib.Algebra.Group.Subgroup.Basic
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Matrix.Mul
import Mathlib.Data.Fin.VecNotation
import Mathlib.RingTheory.OrderOfVanishing.Basic
import Mathlib.RingTheory.Ideal.Quotient.Operations
import Mathlib.RingTheory.KrullDimension.PID
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring
import Mathlib.Algebra.Algebra.Basic
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.Algebra.Module.LinearMap.Defs
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.RingTheory.Valuation.ValuationRing
import Mathlib.LinearAlgebra.Matrix.Adjugate
import Mathlib.LinearAlgebra.Trace
import Mathlib.RingTheory.Ideal.Quotient.Basic
import Mathlib.LinearAlgebra.Matrix.ToLinearEquiv
import Mathlib.LinearAlgebra.Dimension.Free
import Mathlib.GroupTheory.Abelianization.Defs
import Mathlib.Algebra.Group.TypeTags.Basic
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
import Theorems.Thm_Module_length_quotient_le_of_inertia_leibniz_family
import Theorems.Thm_GaloisRepAdic_conj_mul_conj_eq_pow_of_isUnipotentOnInertiaAt
import Theorems.Thm_GaloisRepAdic_det_eq_one_of_mem_inertiaSubgroupIn
import Theorems.Thm_Matrix_exists_adapted_basis_of_unipotent_family
import Theorems.Thm_Matrix_exists_adapted_frob_shape
import Theorems.Thm_GaloisRep_DeformationRingData_forall_apply_eq_zero_of_forall_toCotangent_trace
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_GaloisRep_DeformationRingData_length_level_quotient_le_of_isUnipotentOnInertiaAt

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

open scoped Pointwise

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
p2m_reactivate "P2MW.S_GaloisRep_DeformationRingData_length_level_quotient_le_of_isUnipotentOnInertiaAt.WCOTTameD"

namespace WCOTTameD

variable (𝒪 : Type) [CommRing 𝒪] [IsDomain 𝒪] [IsDiscreteValuationRing 𝒪] (m : ℕ)

abbrev Rm : Type := 𝒪 ⧸ (IsLocalRing.maximalIdeal 𝒪) ^ m

end WCOTTameD
p2m_reactivate "P2MW.S_GaloisRep_DeformationRingData_length_level_quotient_le_of_isUnipotentOnInertiaAt.WCOTTameD"

namespace WCOTTameD

open GaloisRep IsLocalRing TrivSqZeroExt

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

end hK
p2m_reactivate "P2MW.S_GaloisRep_DeformationRingData_length_level_quotient_le_of_isUnipotentOnInertiaAt.WCOTTameD"

end WCOTTameD
p2m_reactivate "P2MW.S_GaloisRep_DeformationRingData_length_level_quotient_le_of_isUnipotentOnInertiaAt.WCOTTameD"

namespace WCOTTameD

open GaloisRep IsLocalRing TrivSqZeroExt

section BHelpers

theorem toMatrix_baseChangeAlong_eq_map {A B' : Type} [CommRing A] [IsLocalRing A]
    [CommRing B'] [IsLocalRing B'] (f : A →+* B') (hf : IsLocalHom f)
    (ρ : GaloisRepAdic A) (b : Module.Basis (Fin 2) A ρ.V) (τ) :
    letI : Algebra A B' := f.toAlgebra
    LinearMap.toMatrix (b.baseChange B') (b.baseChange B') ((ρ.baseChangeAlong f hf).ρ τ) =
      (LinearMap.toMatrix b b (ρ.ρ τ)).map f := by
  letI : Algebra A B' := f.toAlgebra
  show LinearMap.toMatrix (b.baseChange B') (b.baseChange B') ((ρ.ρ τ).baseChange B') =
    (LinearMap.toMatrix b b (ρ.ρ τ)).map f
  ext i j
  simp only [LinearMap.toMatrix_apply, Matrix.map_apply, LinearMap.baseChange_tmul,
    Module.Basis.baseChange_apply, Module.Basis.baseChange_repr_tmul,
    RingHom.smul_toAlgebra, mul_one]

theorem charpoly_baseChangeAlong_eq {A B' : Type} [CommRing A] [IsLocalRing A]
    [CommRing B'] [IsLocalRing B'] (f : A →+* B') (hf : IsLocalHom f)
    (ρ : GaloisRepAdic A) (b : Module.Basis (Fin 2) A ρ.V) (τ) :
    LinearMap.charpoly ((ρ.baseChangeAlong f hf).ρ τ) =
      ((LinearMap.toMatrix b b (ρ.ρ τ)).map f).charpoly := by
  letI : Algebra A B' := f.toAlgebra
  rw [← LinearMap.charpoly_toMatrix ((ρ.baseChangeAlong f hf).ρ τ) (b.baseChange B')]
  exact congrArg Matrix.charpoly (toMatrix_baseChangeAlong_eq_map f hf ρ b τ)

theorem charpoly_baseChangeAlong_conj {A B' : Type} [CommRing A] [IsLocalRing A]
    [CommRing B'] [IsLocalRing B'] (f : A →+* B') (hf : IsLocalHom f)
    (ρ : GaloisRepAdic A) (b : Module.Basis (Fin 2) A ρ.V) (g τ) :
    LinearMap.charpoly ((ρ.baseChangeAlong f hf).ρ (g * τ * g⁻¹)) =
      LinearMap.charpoly ((ρ.baseChangeAlong f hf).ρ τ) := by
  rw [charpoly_baseChangeAlong_eq f hf ρ b, charpoly_baseChangeAlong_eq f hf ρ b]

  let F : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) →* Matrix (Fin 2) (Fin 2) B' :=
    (RingHom.mapMatrix (m := Fin 2) f).toMonoidHom.comp
      (((LinearMap.toMatrixAlgEquiv b).toRingEquiv.toRingHom : Module.End A ρ.V →+*
          Matrix (Fin 2) (Fin 2) A).toMonoidHom.comp ρ.ρ)
  have hF : ∀ h, (LinearMap.toMatrix b b (ρ.ρ h)).map f = F h := fun _ => rfl
  rw [hF, hF, map_mul, map_mul, Matrix.charpoly_mul_comm, ← mul_assoc, ← map_mul,
    inv_mul_cancel, map_one, one_mul]

end BHelpers
p2m_reactivate "P2MW.S_GaloisRep_DeformationRingData_length_level_quotient_le_of_isUnipotentOnInertiaAt.WCOTTameD"

theorem trace_eq_two_of_charpoly_eq_sq {R : Type} [CommRing R] [Nontrivial R]
    (M : Matrix (Fin 2) (Fin 2) R)
    (h : M.charpoly = (Polynomial.X - 1) ^ 2) : M.trace = 2 := by
  rw [Matrix.charpoly_fin_two] at h
  have hc := congrArg (·.coeff 1) h
  simp only [Polynomial.coeff_add, Polynomial.coeff_sub, Polynomial.coeff_X_pow,
    Polynomial.coeff_C, if_pos trivial, if_neg (by decide : ¬ (1 : ℕ) = 2),
    if_neg (by decide : ¬ (1 : ℕ) = 0), mul_one, sub_sq, one_pow, Polynomial.coeff_one,
    Polynomial.coeff_ofNat_mul, Polynomial.coeff_mul_X, Polynomial.coeff_X] at hc
  linear_combination -hc

section AdjTrace

variable {𝒪 : Type} [CommRing 𝒪] {B : Type} [CommRing B] [Algebra 𝒪 B]
  (x : B →ₐ[𝒪] 𝒪) {V : Type} [AddCommGroup V] [Module B V] (b : Module.Basis (Fin 2) B V)
  (G : Type) (ρ : G → V →ₗ[B] V)

theorem adjTrace_Λₗ_eq {M : Type} [CommRing M] [Algebra 𝒪 M]
    (φ : (RingHom.ker (x : B →+* 𝒪)).Cotangent →ₗ[𝒪] M) (τ : G) :
    φ (cotOfEntry x (Matrix.det (LinearMap.toMatrix b b (ρ τ)))) =
      Matrix.trace (Matrix.adjugate (Fbar x b G ρ M τ) * Λₗ x b G ρ φ τ) := by
  set Mτ := LinearMap.toMatrix b b (ρ τ)

  rw [Matrix.det_fin_two, map_sub,
    cotOfEntry_apply, cotOfEntry_apply,
    toCotangent_δ_mul, toCotangent_δ_mul, map_sub, map_add, map_add, map_smul, map_smul,
    map_smul, map_smul, Algebra.smul_def, Algebra.smul_def, Algebra.smul_def, Algebra.smul_def]

  rw [Matrix.adjugate_fin_two, Matrix.trace_fin_two, Matrix.mul_apply, Matrix.mul_apply,
    Fin.sum_univ_two, Fin.sum_univ_two]
  simp only [Fbar_apply, Λₗ_apply, cotOfEntry_apply, Matrix.of_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one]
  ring

end AdjTrace
p2m_reactivate "P2MW.S_GaloisRep_DeformationRingData_length_level_quotient_le_of_isUnipotentOnInertiaAt.WCOTTameD"

end WCOTTameD
p2m_reactivate "P2MW.S_GaloisRep_DeformationRingData_length_level_quotient_le_of_isUnipotentOnInertiaAt.WCOTTameD"

namespace WCOTTameD

open GaloisRep IsLocalRing

section rowHKB
variable {𝒪 : Type} [CommRing 𝒪] [IsDomain 𝒪] [IsDiscreteValuationRing 𝒪]
  [IsAdicComplete (IsLocalRing.maximalIdeal 𝒪) 𝒪]
  {ρbar : ResidualGaloisRep (IsLocalRing.ResidueField 𝒪)}
  {𝒟₀ 𝒟' : ∀ ⦃A : Type⦄ [CommRing A] [IsLocalRing A] [Algebra 𝒪 A], GaloisRepAdic A → Prop}
  (D₀ : DeformationRingData 𝒪 ρbar 𝒟₀) (D' : DeformationRingData 𝒪 ρbar 𝒟')
  (θ : D'.R →ₐ[𝒪] D₀.R) (x₀ : D₀.R →ₐ[𝒪] 𝒪)

theorem trace_Λₗspec_eq (m : ℕ) (φ : Φ' D₀ D' θ x₀ →ₗ[𝒪] Rm 𝒪 m)
    (τ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) :
    Matrix.trace (Λₗspec D₀ D' θ x₀ m φ τ) =
      φ ((RingHom.ker (xPrime D₀ D' θ x₀ : D'.R →+* 𝒪)).toCotangent
        (δ (xPrime D₀ D' θ x₀) (LinearMap.trace D'.R D'.ρ.V (D'.ρ.ρ τ)))) := by
  rw [Matrix.trace_fin_two]
  change φ (cotOfEntry (xPrime D₀ D' θ x₀) (LinearMap.toMatrix (bD D') (bD D') (D'.ρ.ρ τ) 0 0)) +
      φ (cotOfEntry (xPrime D₀ D' θ x₀) (LinearMap.toMatrix (bD D') (bD D') (D'.ρ.ρ τ) 1 1)) = _
  rw [← map_add, ← map_add, ← Matrix.trace_fin_two (LinearMap.toMatrix (bD D') (bD D') (D'.ρ.ρ τ)),
    ← LinearMap.trace_eq_matrix_trace D'.R (bD D') (D'.ρ.ρ τ), cotOfEntry_apply]

end rowHKB
p2m_reactivate "P2MW.S_GaloisRep_DeformationRingData_length_level_quotient_le_of_isUnipotentOnInertiaAt.WCOTTameD"

end WCOTTameD
p2m_reactivate "P2MW.S_GaloisRep_DeformationRingData_length_level_quotient_le_of_isUnipotentOnInertiaAt.WCOTTameD"

namespace WCOTConjFam

variable {𝒪 : Type} [CommRing 𝒪] {R : Type} [CommRing R] [Algebra 𝒪 R] {G : Type}
  {H : Type} [AddCommGroup H] [Module 𝒪 H]

theorem conj_two_sided (U U' : Matrix (Fin 2) (Fin 2) R) (h : U * U' = 1) : U' * U = 1 :=
  mul_eq_one_comm.mp h

def conjFam (U U' : Matrix (Fin 2) (Fin 2) R) (Λ : H →ₗ[𝒪] (G → Matrix (Fin 2) (Fin 2) R)) :
    H →ₗ[𝒪] (G → Matrix (Fin 2) (Fin 2) R) where
  toFun φ g := U' * Λ φ g * U
  map_add' φ ψ := by
    funext g
    simp only [map_add, Pi.add_apply, Matrix.mul_add, Matrix.add_mul]
  map_smul' c φ := by
    funext g
    simp only [map_smul, Pi.smul_apply, Matrix.mul_smul, Matrix.smul_mul, RingHom.id_apply]

theorem conjFam_apply (U U' : Matrix (Fin 2) (Fin 2) R) (Λ : H →ₗ[𝒪] (G → Matrix (Fin 2) (Fin 2) R)) (φ : H) (g : G) :
    conjFam U U' Λ φ g = U' * Λ φ g * U := rfl

theorem conj_mul [Mul G] (U U' : Matrix (Fin 2) (Fin 2) R) (hUU' : U * U' = 1) (F : G → Matrix (Fin 2) (Fin 2) R)
    (hFmul : ∀ g h : G, F (g * h) = F g * F h) (g h : G) :
    U' * F (g * h) * U = (U' * F g * U) * (U' * F h * U) := by
  rw [hFmul]
  calc U' * (F g * F h) * U = U' * (F g * (U * U') * F h) * U := by rw [hUU', Matrix.mul_one]
    _ = (U' * F g * U) * (U' * F h * U) := by simp only [Matrix.mul_assoc]

theorem conj_one [One G] (U U' : Matrix (Fin 2) (Fin 2) R) (hU'U : U' * U = 1) (F : G → Matrix (Fin 2) (Fin 2) R)
    (hF1 : F 1 = 1) : U' * F 1 * U = 1 := by
  rw [hF1, Matrix.mul_one, hU'U]

theorem conj_leibniz [Mul G] (U U' : Matrix (Fin 2) (Fin 2) R) (hUU' : U * U' = 1) (F : G → Matrix (Fin 2) (Fin 2) R)
    (Λ : G → Matrix (Fin 2) (Fin 2) R) (hLeib : ∀ g h : G, Λ (g * h) = F g * Λ h + Λ g * F h) (g h : G) :
    U' * Λ (g * h) * U = (U' * F g * U) * (U' * Λ h * U) + (U' * Λ g * U) * (U' * F h * U) := by
  rw [hLeib]
  calc U' * (F g * Λ h + Λ g * F h) * U
        = U' * (F g * (U * U') * Λ h + Λ g * (U * U') * F h) * U := by rw [hUU', Matrix.mul_one, Matrix.mul_one]
    _ = (U' * F g * U) * (U' * Λ h * U) + (U' * Λ g * U) * (U' * F h * U) := by
          simp only [Matrix.mul_add, Matrix.add_mul, Matrix.mul_assoc]

theorem conjFam_leibniz [Mul G] (U U' : Matrix (Fin 2) (Fin 2) R) (hUU' : U * U' = 1) (F : G → Matrix (Fin 2) (Fin 2) R)
    (Λ : H →ₗ[𝒪] (G → Matrix (Fin 2) (Fin 2) R)) (hLeib : ∀ (φ : H) (g h : G), Λ φ (g * h) = F g * Λ φ h + Λ φ g * F h)
    (φ : H) (g h : G) :
    conjFam U U' Λ φ (g * h) =
      (U' * F g * U) * conjFam U U' Λ φ h + conjFam U U' Λ φ g * (U' * F h * U) := by
  simp only [conjFam_apply]
  exact conj_leibniz U U' hUU' F (Λ φ) (hLeib φ) g h

end WCOTConjFam
p2m_reactivate "P2MW.S_GaloisRep_DeformationRingData_length_level_quotient_le_of_isUnipotentOnInertiaAt.WCOTTameD"

open Polynomial

namespace WCOTAdapt

variable {R : Type} [CommRing R]

private def _root_.WCOTAdapt.sl2M (s t u : R) : Matrix (Fin 2) (Fin 2) R := Matrix.of ![![s, t], ![u, -s]]

p2m_export "WCOTAdapt" "sl2M"

theorem trace_eq_two_and_sq_eq_zero_of_charpoly [Nontrivial R]
    (M : Matrix (Fin 2) (Fin 2) R) (h : M.charpoly = (X - 1) ^ 2) :
    M.trace = 2 ∧ M.det = 1 ∧ (M - 1) * (M - 1) = 0 := by
  have hch : (X : R[X]) ^ 2 - C M.trace * X + C M.det = (X - 1) ^ 2 := by
    rw [← Matrix.charpoly_fin_two]; exact h
  have hexp : ((X : R[X]) - 1) ^ 2 = X ^ 2 - C 2 * X + C 1 := by
    rw [map_ofNat, map_one]; ring
  rw [hexp] at hch
  have e1 : M.trace = 2 := by
    have h1 := congrArg (fun p => Polynomial.coeff p 1) hch
    simp only [Polynomial.coeff_add, Polynomial.coeff_sub, Polynomial.coeff_C_mul,
      Polynomial.coeff_X_one, Polynomial.coeff_X_pow, Polynomial.coeff_C, mul_one] at h1
    simpa using h1
  have e0 : M.det = 1 := by
    have h0 := congrArg (fun p => Polynomial.coeff p 0) hch
    simp only [Polynomial.coeff_add, Polynomial.coeff_sub, Polynomial.coeff_C_mul,
      Polynomial.coeff_X_zero, Polynomial.coeff_X_pow, Polynomial.coeff_C, mul_zero] at h0
    simpa using h0
  have hCH := Matrix.aeval_self_charpoly M
  rw [h] at hCH
  have hsq : (M - 1) ^ 2 = 0 := by
    simpa [map_pow, map_sub, Polynomial.aeval_X] using hCH
  exact ⟨e1, e0, by rw [← pow_two]; exact hsq⟩

theorem exists_adapted_basis [IsDomain R] [ValuationRing R]
    (T : Set (Matrix (Fin 2) (Fin 2) R))
    (hmul : ∀ A ∈ T, ∀ B ∈ T, A * B ∈ T)
    (hsq : ∀ A ∈ T, (A - 1) * (A - 1) = 0)
    (A₀ : Matrix (Fin 2) (Fin 2) R) (hA₀ : A₀ ∈ T) (hA₀ne : A₀ ≠ 1) :
    ∃ P : Matrix (Fin 2) (Fin 2) R, IsUnit P.det ∧
      (∃ t : R, t ≠ 0 ∧ A₀ * P = P * (1 + sl2M 0 t 0)) ∧
      ∀ A ∈ T, ∃ s : R, A * P = P * (1 + sl2M 0 s 0) := by
  have key : ∀ s : R, (1 + sl2M 0 s 0 : Matrix (Fin 2) (Fin 2) R) = Matrix.of ![![1, s], ![0, 1]] := by
    intro s; ext i j; fin_cases i <;> fin_cases j <;> simp [sl2M]
  obtain ⟨P, hP, ⟨t, ht, h0⟩, hall⟩ :=
    Matrix.exists_adapted_basis_of_unipotent_family T hmul hsq A₀ hA₀ hA₀ne
  exact ⟨P, hP, ⟨t, ht, by rw [key]; exact h0⟩, fun A hA => by
    obtain ⟨s, hs⟩ := hall A hA; exact ⟨s, by rw [key]; exact hs⟩⟩

theorem adapted_frob_shape [IsDomain R]
    (N₀ P F : Matrix (Fin 2) (Fin 2) R) (hP : IsUnit P.det)
    (t : R) (ht : t ≠ 0) (hN₀P : N₀ * P = P * sl2M 0 t 0)
    (q : R) (hFN : F * N₀ = q • (N₀ * F)) :
    ∃ F' : Matrix (Fin 2) (Fin 2) R,
      F * P = P * F' ∧ F' 1 0 = 0 ∧ F' 0 0 = q * F' 1 1 := by
  have key : (sl2M 0 t 0 : Matrix (Fin 2) (Fin 2) R) = Matrix.of ![![0, t], ![0, 0]] := by
    ext i j; fin_cases i <;> fin_cases j <;> simp [sl2M]
  rw [key] at hN₀P
  exact Matrix.exists_adapted_frob_shape N₀ P F hP t ht hN₀P q hFN

theorem shape_map {S : Type} [CommRing S] (f : R →+* S)
    (A P : Matrix (Fin 2) (Fin 2) R) (s : R) (h : A * P = P * (1 + sl2M 0 s 0)) :
    A.map f * P.map f = P.map f * (1 + sl2M 0 (f s) 0) := by
  have h2 : (A * P).map f = (P * (1 + sl2M 0 s 0)).map f := by rw [h]
  rw [Matrix.map_mul, Matrix.map_mul] at h2
  rw [h2]
  congr 1
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [sl2M, Matrix.map_apply]

theorem isUnit_det_map {S : Type} [CommRing S] (f : R →+* S)
    (P : Matrix (Fin 2) (Fin 2) R) (hP : IsUnit P.det) : IsUnit (P.map f).det := by
  have h := f.map_det P
  rw [show (f.mapMatrix P) = P.map f from rfl] at h
  rw [← h]
  exact hP.map f

end WCOTAdapt
p2m_reactivate "P2MW.S_GaloisRep_DeformationRingData_length_level_quotient_le_of_isUnipotentOnInertiaAt.WCOTTameD"

namespace WCOTBridge

variable {R : Type} [CommRing R]

private def _root_.WCOTBridge.sl2M (s t u : R) : Matrix (Fin 2) (Fin 2) R := Matrix.of ![![s, t], ![u, -s]]

p2m_export "WCOTBridge" "sl2M"

theorem trace_adjugate_conj (F Λ U U' : Matrix (Fin 2) (Fin 2) R)
    (hU'U : U' * U = 1) :
    (Matrix.adjugate (U' * F * U) * (U' * Λ * U)).trace = (Matrix.adjugate F * Λ).trace := by
  have hdet : U'.det * U.det = 1 := by
    rw [← Matrix.det_mul, hU'U, Matrix.det_one]
  rw [Matrix.adjugate_mul_distrib, Matrix.adjugate_mul_distrib]

  have key : (Matrix.adjugate U * (Matrix.adjugate F * Matrix.adjugate U')) * (U' * Λ * U)
      = Matrix.adjugate U * (Matrix.adjugate F * (U'.det • 1) * Λ * U) := by
    rw [← Matrix.adjugate_mul U']
    simp only [Matrix.mul_assoc]
  rw [key]
  have key2 : Matrix.adjugate U * (Matrix.adjugate F * (U'.det • 1) * Λ * U)
      = U'.det • (Matrix.adjugate U * (Matrix.adjugate F * Λ * U)) := by
    simp only [Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one]
  rw [key2, Matrix.trace_smul]
  rw [Matrix.trace_mul_comm]

  have key3 : Matrix.adjugate F * Λ * U * Matrix.adjugate U
      = Matrix.adjugate F * Λ * (U.det • 1) := by
    rw [Matrix.mul_assoc, Matrix.mul_adjugate]
  rw [key3, Matrix.mul_smul, Matrix.mul_one, Matrix.trace_smul]
  rw [smul_eq_mul, smul_eq_mul, ← mul_assoc, hdet, one_mul]

theorem trace_eq_zero_of_adjugate_trace (Fb Λ U U' : Matrix (Fin 2) (Fin 2) R)
    (hUU' : U * U' = 1) (hU'U : U' * U = 1)
    (a : R) (hFb : U' * Fb * U = 1 + sl2M 0 a 0)
    (hadj : (Matrix.adjugate Fb * Λ).trace = 0)
    (hu : (U' * Λ * U) 1 0 = 0) :
    Λ.trace = 0 := by
  have h1 : (Matrix.adjugate (U' * Fb * U) * (U' * Λ * U)).trace = 0 := by
    rw [trace_adjugate_conj Fb Λ U U' hU'U]; exact hadj
  rw [hFb] at h1
  have hadjFb : Matrix.adjugate (1 + sl2M 0 a 0) = 1 + sl2M 0 (-a) 0 := by
    rw [Matrix.adjugate_fin_two]
    ext i j; fin_cases i <;> fin_cases j <;> simp [sl2M]
  rw [hadjFb] at h1
  have hexp : ((1 + sl2M 0 (-a) 0) * (U' * Λ * U)).trace
      = (U' * Λ * U).trace + (-a) * (U' * Λ * U) 1 0 := by
    rw [add_mul, Matrix.one_mul, Matrix.trace_add]
    congr 1
    rw [Matrix.trace_fin_two]
    simp [sl2M, Matrix.mul_apply, Fin.sum_univ_two]
  rw [hexp, hu, mul_zero, add_zero] at h1

  rw [Matrix.trace_mul_comm, ← Matrix.mul_assoc, hUU', Matrix.one_mul] at h1
  exact h1

end WCOTBridge
p2m_reactivate "P2MW.S_GaloisRep_DeformationRingData_length_level_quotient_le_of_isUnipotentOnInertiaAt.WCOTTameD"

namespace WCOTLadderB

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

theorem one_add_pow_of_sq_eq_zero {R : Type} [CommRing R] (N : Matrix (Fin 2) (Fin 2) R)
    (hN : N * N = 0) (k : ℕ) : (1 + N) ^ k = 1 + (k : R) • N := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [pow_succ, ih, mul_add, mul_one, add_mul, one_mul, smul_mul_assoc, hN, smul_zero,
      add_zero, Nat.cast_succ, add_smul, one_smul]
    abel

open scoped Pointwise

set_option maxSynthPendingDepth 3 in

theorem hK_of_row13a
    (hx₀ : IsLocalHom (x₀ : D₀.R →+* 𝒪)) (hθ : IsLocalHom (θ : D'.R →+* D₀.R)) (m : ℕ) [NeZero m]
    (p q : ℕ) (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q)
    (P : ValuationSubring (AlgebraicClosure ℚ)) (hP : P.LiesOverPrime q)
    (hθρ : (D'.ρ.baseChangeAlong (θ : D'.R →+* D₀.R) hθ).IsEquiv D₀.ρ)
    (hθsurj : Function.Surjective (θ : D'.R →+* D₀.R))
    (hconj : ∀ P' : ValuationSubring (AlgebraicClosure ℚ), P'.LiesOverPrime q →
      ∃ g : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ, g • P = P')
    (hur : haveI := isLocalHom_xPrime D₀ D' θ x₀ hx₀ hθ
      (D'.ρ.baseChangeAlong (xPrime D₀ D' θ x₀ : D'.R →+* 𝒪)
        (isLocalHom_xPrime D₀ D' θ x₀ hx₀ hθ)).IsUnipotentOnInertiaAt q)
    (Hdet : ∀ {A : Type} [CommRing A] [IsLocalRing A] [Algebra 𝒪 A] (ρA : GaloisRepAdic A),
      𝒟' ρA → ρA.DetIsCyclotomic p)
    (H1 : ∀ {A : Type} [CommRing A] [IsLocalRing A] [Algebra 𝒪 A] (ρA : GaloisRepAdic A)
        {B : Type} [CommRing B] [IsLocalRing B] [Algebra 𝒪 B] (f : A →+* B) (hf : IsLocalHom f),
      𝒟' ρA → 𝒟' (ρA.baseChangeAlong f hf))
    (H2 : ∀ {A : Type} [CommRing A] [IsLocalRing A] [Algebra 𝒪 A] (ρA : GaloisRepAdic A),
      𝒟' ρA → ρA.IsUnipotentOnInertiaAt q → 𝒟₀ ρA)
    (φ : Φ' D₀ D' θ x₀ →ₗ[𝒪] Rm 𝒪 m)
    (htr0 : ∀ τ ∈ P.inertiaSubgroupIn ℚ, Matrix.trace (Λₗspec D₀ D' θ x₀ m φ τ) = 0) :
    φ ∈ (LinearMap.ker (LinearMap.lcomp 𝒪 (Rm 𝒪 m) (COT1.cotangentRelaxKer D₀ D' θ x₀).subtype) :
      Submodule 𝒪 (Φ' D₀ D' θ x₀ →ₗ[𝒪] Rm 𝒪 m)) := by
  have h := GaloisRep.DeformationRingData.forall_apply_eq_zero_of_forall_toCotangent_trace D₀ D' θ x₀ hx₀ hθ m
    p q hp hq hpq P hP hθρ hθsurj hconj (isLocalHom_xPrime D₀ D' θ x₀ hx₀ hθ) hur Hdet H1 H2 φ
    (fun τ hτ t ht => by
      obtain ⟨t, htm⟩ := t
      change t = _ at ht
      subst ht
      have h0 := htr0 τ hτ
      rw [trace_Λₗspec_eq] at h0
      exact h0)
  refine LinearMap.mem_ker.mpr (LinearMap.ext fun v => ?_)
  exact h v.1 v.2

theorem lengthLevelB
    (hx₀ : IsLocalHom (x₀ : D₀.R →+* 𝒪)) (hθ : IsLocalHom (θ : D'.R →+* D₀.R))
    (hθρ : (D'.ρ.baseChangeAlong (θ : D'.R →+* D₀.R) hθ).IsEquiv D₀.ρ)
    (hθsurj : Function.Surjective (θ : D'.R →+* D₀.R))
    (p q : ℕ) (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q)
    (hp𝔪 : (p : 𝒪) ∈ IsLocalRing.maximalIdeal 𝒪)
    (P : ValuationSubring (AlgebraicClosure ℚ)) (hP : P.LiesOverPrime q)
    (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)
    (hconj : ∀ P' : ValuationSubring (AlgebraicClosure ℚ), P'.LiesOverPrime q →
      ∃ g : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ, g • P = P')
    (hur : haveI := isLocalHom_xPrime D₀ D' θ x₀ hx₀ hθ
      (D'.ρ.baseChangeAlong (xPrime D₀ D' θ x₀ : D'.R →+* 𝒪)
        (isLocalHom_xPrime D₀ D' θ x₀ hx₀ hθ)).IsUnipotentOnInertiaAt q)
    (Hdet : ∀ {A : Type} [CommRing A] [IsLocalRing A] [Algebra 𝒪 A] (ρA : GaloisRepAdic A),
      𝒟' ρA → ρA.DetIsCyclotomic p)
    (H1 : ∀ {A : Type} [CommRing A] [IsLocalRing A] [Algebra 𝒪 A] (ρA : GaloisRepAdic A)
        {B : Type} [CommRing B] [IsLocalRing B] [Algebra 𝒪 B] (f : A →+* B) (hf : IsLocalHom f),
      𝒟' ρA → 𝒟' (ρA.baseChangeAlong f hf))
    (H2 : ∀ {A : Type} [CommRing A] [IsLocalRing A] [Algebra 𝒪 A] (ρA : GaloisRepAdic A),
      𝒟' ρA → ρA.IsUnipotentOnInertiaAt q → 𝒟₀ ρA)
    (hdivI : ∀ (k : ℕ) (τ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ),
      τ ∈ P.inertiaSubgroupIn ℚ →
      ∃ w : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ, w ∈ P.inertiaSubgroupIn ℚ ∧
        w ^ (p ^ k) = σ * τ * σ⁻¹ * (τ ^ q)⁻¹)
    (hgen : ∀ m : ℕ, ∃ γ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ,
      γ ∈ P.inertiaSubgroupIn ℚ ∧
      ∀ τ ∈ P.inertiaSubgroupIn ℚ, ∃ (j : ℕ) (x w : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ),
        x ∈ P.inertiaSubgroupIn ℚ ∧ w ∈ P.inertiaSubgroupIn ℚ ∧
        τ = γ ^ j * x ^ (p ^ m) * w ^ (p ^ m))
    (n : ℕ) :
    Module.length 𝒪 (((RingHom.ker (x₀.comp θ : D'.R →ₐ[𝒪] 𝒪)).Cotangent →ₗ[𝒪]
        𝒪 ⧸ (IsLocalRing.maximalIdeal 𝒪) ^ (n + 1)) ⧸
      LinearMap.ker (LinearMap.lcomp 𝒪 (𝒪 ⧸ (IsLocalRing.maximalIdeal 𝒪) ^ (n + 1))
        (COT1.cotangentRelaxKer D₀ D' θ x₀).subtype)) ≤
    Module.length 𝒪 (𝒪 ⧸ Ideal.span {(q : 𝒪) ^ 2 - 1}) := by
  classical
  have hx' : IsLocalHom (xPrime D₀ D' θ x₀ : D'.R →+* 𝒪) := isLocalHom_xPrime D₀ D' θ x₀ hx₀ hθ

  set Mof : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) → Matrix (Fin 2) (Fin 2) 𝒪 :=
    fun g => (LinearMap.toMatrix (bD D') (bD D') (D'.ρ.ρ g)).map (xPrime D₀ D' θ x₀ : D'.R →+* 𝒪)
    with hMofdef
  have hMofmul : ∀ g h : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ,
      Mof (g * h) = Mof g * Mof h := by
    intro g h
    simp only [hMofdef]
    rw [map_mul (D'.ρ.ρ), LinearMap.toMatrix_mul (bD D'), Matrix.map_mul]
  have hMof1 : Mof 1 = 1 := by
    simp only [hMofdef]
    rw [map_one (D'.ρ.ρ), LinearMap.toMatrix_one, Matrix.map_one _ (map_zero _) (map_one _)]

  have hFbarR : ∀ g : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ,
      Fbar (xPrime D₀ D' θ x₀) (bD D') (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)
        (fun g => D'.ρ.ρ g) (𝒪 ⧸ (IsLocalRing.maximalIdeal 𝒪) ^ (n + 1)) g
        = (Mof g).map (algebraMap 𝒪 (𝒪 ⧸ (IsLocalRing.maximalIdeal 𝒪) ^ (n + 1))) := by
    intro g
    ext i j
    simp only [Fbar_apply, hMofdef, Matrix.map_apply]
    rfl

  have hdet1 : ∀ τ ∈ P.inertiaSubgroupIn ℚ,
      ∃ c, Matrix.det (LinearMap.toMatrix (bD D') (bD D') (D'.ρ.ρ τ)) = algebraMap 𝒪 D'.R c := by
    intro τ hτ
    refine ⟨1, ?_⟩
    rw [map_one, LinearMap.det_toMatrix]
    exact GaloisRepAdic.det_eq_one_of_mem_inertiaSubgroupIn D'.ρ hp hq hpq (Hdet D'.ρ D'.isOfType) P hP τ hτ
  by_cases htriv : ∀ τ ∈ P.inertiaSubgroupIn ℚ, Mof τ = 1
  ·
    have hker : LinearMap.ker (LinearMap.lcomp 𝒪 (𝒪 ⧸ (IsLocalRing.maximalIdeal 𝒪) ^ (n + 1))
        (COT1.cotangentRelaxKer D₀ D' θ x₀).subtype) = ⊤ := by
      rw [eq_top_iff]
      intro φ _
      refine hK_of_row13a D₀ D' θ x₀ hx₀ hθ (n + 1) p q hp hq hpq P hP hθρ hθsurj hconj hur
        @Hdet @H1 @H2 φ ?_
      intro τ hτ
      refine trace_Λₗ_eq_zero (xPrime D₀ D' θ x₀) (bD D') _ (D'.ρ.ρ) φ τ ?_ (hdet1 τ hτ)
      rw [hFbarR τ, htriv τ hτ]
      exact Matrix.map_one _ (map_zero _) (map_one _)
    rw [hker]
    haveI : Subsingleton ((((RingHom.ker (x₀.comp θ : D'.R →ₐ[𝒪] 𝒪)).Cotangent →ₗ[𝒪]
        𝒪 ⧸ (IsLocalRing.maximalIdeal 𝒪) ^ (n + 1))) ⧸
        (⊤ : Submodule 𝒪 ((RingHom.ker (x₀.comp θ : D'.R →ₐ[𝒪] 𝒪)).Cotangent →ₗ[𝒪]
          𝒪 ⧸ (IsLocalRing.maximalIdeal 𝒪) ^ (n + 1)))) := by
      refine ⟨fun a b => ?_⟩
      induction a using Quotient.inductionOn' with
      | h x =>
        induction b using Quotient.inductionOn' with
        | h y => exact (Submodule.Quotient.eq _).mpr trivial
    rw [Module.length_eq_zero]
    exact zero_le
  ·
    push Not at htriv
    obtain ⟨τ₀, hτ₀I, hτ₀ne⟩ := htriv

    have hcp : ∀ τ ∈ P.inertiaSubgroupIn ℚ, (Mof τ).charpoly = (Polynomial.X - 1) ^ 2 := by
      intro τ hτ
      have h := hur P hP τ hτ
      rwa [charpoly_baseChangeAlong_eq (xPrime D₀ D' θ x₀ : D'.R →+* 𝒪) hx' D'.ρ (bD D') τ] at h
    have hpack : ∀ τ ∈ P.inertiaSubgroupIn ℚ,
        (Mof τ).trace = 2 ∧ (Mof τ).det = 1 ∧ (Mof τ - 1) * (Mof τ - 1) = 0 :=
      fun τ hτ => WCOTAdapt.trace_eq_two_and_sq_eq_zero_of_charpoly _ (hcp τ hτ)

    have hTmul : ∀ A ∈ {A | ∃ τ ∈ P.inertiaSubgroupIn ℚ, Mof τ = A},
        ∀ B ∈ {A | ∃ τ ∈ P.inertiaSubgroupIn ℚ, Mof τ = A},
        A * B ∈ {A | ∃ τ ∈ P.inertiaSubgroupIn ℚ, Mof τ = A} := by
      rintro A ⟨τ₁, hτ₁, rfl⟩ B ⟨τ₂, hτ₂, rfl⟩
      exact ⟨τ₁ * τ₂, mul_mem hτ₁ hτ₂, hMofmul τ₁ τ₂⟩
    have hTsq : ∀ A ∈ {A | ∃ τ ∈ P.inertiaSubgroupIn ℚ, Mof τ = A}, (A - 1) * (A - 1) = 0 := by
      rintro A ⟨τ, hτ, rfl⟩
      exact (hpack τ hτ).2.2
    obtain ⟨Pad, hPdet, ⟨t, ht, hA₀P⟩, hall⟩ :=
      WCOTAdapt.exists_adapted_basis {A | ∃ τ ∈ P.inertiaSubgroupIn ℚ, Mof τ = A}
        hTmul hTsq (Mof τ₀) ⟨τ₀, hτ₀I, rfl⟩ hτ₀ne
    haveI := Pad.invertibleOfIsUnitDet hPdet

    have htameE := GaloisRepAdic.conj_mul_conj_eq_pow_of_isUnipotentOnInertiaAt
      (D'.ρ.baseChangeAlong (xPrime D₀ D' θ x₀ : D'.R →+* 𝒪) hx') q hur P hP σ p hp𝔪 hdivI τ₀ hτ₀I
    letI : Algebra D'.R 𝒪 := (xPrime D₀ D' θ x₀ : D'.R →+* 𝒪).toAlgebra
    have hdict : ∀ g : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ,
        LinearMap.toMatrix ((bD D').baseChange 𝒪) ((bD D').baseChange 𝒪)
          ((D'.ρ.baseChangeAlong (xPrime D₀ D' θ x₀ : D'.R →+* 𝒪) hx').ρ g) = Mof g :=
      fun g => toMatrix_baseChangeAlong_eq_map (xPrime D₀ D' θ x₀ : D'.R →+* 𝒪) hx' D'.ρ (bD D') g
    have hmul2 : ∀ f g : (D'.ρ.baseChangeAlong (xPrime D₀ D' θ x₀ : D'.R →+* 𝒪) hx').V →ₗ[𝒪]
          (D'.ρ.baseChangeAlong (xPrime D₀ D' θ x₀ : D'.R →+* 𝒪) hx').V,
        LinearMap.toMatrix ((bD D').baseChange 𝒪) ((bD D').baseChange 𝒪) (f * g)
          = LinearMap.toMatrix ((bD D').baseChange 𝒪) ((bD D').baseChange 𝒪) f
            * LinearMap.toMatrix ((bD D').baseChange 𝒪) ((bD D').baseChange 𝒪) g :=
      fun f g => LinearMap.toMatrix_mul ((bD D').baseChange 𝒪) f g
    have hone2 : LinearMap.toMatrix ((bD D').baseChange 𝒪) ((bD D').baseChange 𝒪)
        (1 : (D'.ρ.baseChangeAlong (xPrime D₀ D' θ x₀ : D'.R →+* 𝒪) hx').V →ₗ[𝒪]
          (D'.ρ.baseChangeAlong (xPrime D₀ D' θ x₀ : D'.R →+* 𝒪) hx').V) = 1 :=
      LinearMap.toMatrix_one ((bD D').baseChange 𝒪)
    have htoMpow : ∀ (f : (D'.ρ.baseChangeAlong (xPrime D₀ D' θ x₀ : D'.R →+* 𝒪) hx').V →ₗ[𝒪]
          (D'.ρ.baseChangeAlong (xPrime D₀ D' θ x₀ : D'.R →+* 𝒪) hx').V) (k : ℕ),
        LinearMap.toMatrix ((bD D').baseChange 𝒪) ((bD D').baseChange 𝒪) (f ^ k)
          = (LinearMap.toMatrix ((bD D').baseChange 𝒪) ((bD D').baseChange 𝒪) f) ^ k := by
      intro f k
      induction k with
      | zero => rw [pow_zero, pow_zero]; exact hone2
      | succ k ih => rw [pow_succ, pow_succ, hmul2, ih]
    have htameM : Mof σ * Mof τ₀ * Mof σ⁻¹ = Mof τ₀ ^ q := by
      have h1 := congrArg
        (LinearMap.toMatrix ((bD D').baseChange 𝒪) ((bD D').baseChange 𝒪)) htameE
      rw [hmul2, hmul2, htoMpow, hdict, hdict, hdict] at h1
      exact h1

    have hN₀sq : (Mof τ₀ - 1) * (Mof τ₀ - 1) = 0 := (hpack τ₀ hτ₀I).2.2
    have hMτ₀ : Mof τ₀ = 1 + (Mof τ₀ - 1) := by abel
    have hσinv : Mof σ * Mof σ⁻¹ = 1 := by rw [← hMofmul, mul_inv_cancel, hMof1]
    have hinvσ : Mof σ⁻¹ * Mof σ = 1 := by rw [← hMofmul, inv_mul_cancel, hMof1]
    have hFN : Mof σ * (Mof τ₀ - 1) = (q : 𝒪) • ((Mof τ₀ - 1) * Mof σ) := by
      have h1 : Mof σ * Mof τ₀ * Mof σ⁻¹ = 1 + (q : 𝒪) • (Mof τ₀ - 1) := by
        rw [htameM]
        conv_lhs => rw [hMτ₀]
        rw [one_add_pow_of_sq_eq_zero _ hN₀sq]
      have h2 : Mof σ * (Mof τ₀ - 1) * Mof σ⁻¹ = (q : 𝒪) • (Mof τ₀ - 1) := by
        have h3 : Mof σ * (Mof τ₀ - 1) * Mof σ⁻¹
            = Mof σ * Mof τ₀ * Mof σ⁻¹ - Mof σ * Mof σ⁻¹ := by
          rw [mul_sub, mul_one, sub_mul]
        rw [h3, h1, hσinv]
        abel
      have h4 := congrArg (· * Mof σ) h2
      simpa [Matrix.mul_assoc, hinvσ, smul_mul_assoc] using h4
    have hN₀P : (Mof τ₀ - 1) * Pad = Pad * WCOTAdapt.sl2M 0 t 0 := by
      rw [sub_mul, one_mul, hA₀P, mul_add, mul_one]
      abel
    obtain ⟨F', hF'P, hF'10, hF'ratio⟩ :=
      WCOTAdapt.adapted_frob_shape (Mof τ₀ - 1) Pad (Mof σ) hPdet t ht hN₀P ((q : ℕ) : 𝒪) hFN

    set π : 𝒪 →+* (𝒪 ⧸ (IsLocalRing.maximalIdeal 𝒪) ^ (n + 1)) :=
      algebraMap 𝒪 (𝒪 ⧸ (IsLocalRing.maximalIdeal 𝒪) ^ (n + 1)) with hπdef
    have hUmUm' : Pad.map π * (⅟Pad).map π = 1 := by
      rw [← Matrix.map_mul, mul_invOf_self]
      exact Matrix.map_one _ (map_zero _) (map_one _)
    have hUm'Um : (⅟Pad).map π * Pad.map π = 1 := by
      rw [← Matrix.map_mul, invOf_mul_self]
      exact Matrix.map_one _ (map_zero _) (map_one _)
    have hFbRmul : ∀ g h : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ,
        (Mof (g * h)).map π = (Mof g).map π * (Mof h).map π := by
      intro g h
      rw [hMofmul, Matrix.map_mul]
    have hFbR1 : (Mof 1).map π = 1 := by
      rw [hMof1]
      exact Matrix.map_one _ (map_zero _) (map_one _)

    have hLeib₀ : ∀ (φ : Φ' D₀ D' θ x₀ →ₗ[𝒪] Rm 𝒪 (n + 1))
        (g h : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ),
        Λₗspec D₀ D' θ x₀ (n + 1) φ (g * h)
          = (Mof g).map π * Λₗspec D₀ D' θ x₀ (n + 1) φ h
            + Λₗspec D₀ D' θ x₀ (n + 1) φ g * (Mof h).map π := by
      intro φ g h
      have h0 := Λₗ_map_mul' (x := xPrime D₀ D' θ x₀) (b := bD D')
        (G := AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (ρ := fun g => D'.ρ.ρ g)
        (M := 𝒪 ⧸ (IsLocalRing.maximalIdeal 𝒪) ^ (n + 1))
        (fun g₁ g₂ => by
          show D'.ρ.ρ (g₁ * g₂) = D'.ρ.ρ g₁ ∘ₗ D'.ρ.ρ g₂
          rw [map_mul]; rfl) φ g h
      rwa [hFbarR g, hFbarR h] at h0

    have hFI : ∀ τ ∈ P.inertiaSubgroupIn ℚ,
        ((⅟Pad).map π * (Mof τ).map π * Pad.map π) 1 0 = 0 ∧
        ((⅟Pad).map π * (Mof τ).map π * Pad.map π) 0 0 = 1 ∧
        ((⅟Pad).map π * (Mof τ).map π * Pad.map π) 1 1 = 1 := by
      intro τ hτ
      obtain ⟨s, hs⟩ := hall (Mof τ) ⟨τ, hτ, rfl⟩
      have hsm := WCOTAdapt.shape_map π (Mof τ) Pad s hs
      have hshape : (⅟Pad).map π * (Mof τ).map π * Pad.map π
          = 1 + WCOTAdapt.sl2M 0 (π s) 0 := by
        rw [Matrix.mul_assoc, hsm, ← Matrix.mul_assoc, hUm'Um, Matrix.one_mul]
      rw [hshape]
      refine ⟨?_, ?_, ?_⟩ <;> simp [WCOTAdapt.sl2M]

    have hFσc : ((⅟Pad).map π * (Mof σ).map π * Pad.map π) 1 0 = 0 ∧
        ((⅟Pad).map π * (Mof σ).map π * Pad.map π) 0 0
          = (q : 𝒪 ⧸ (IsLocalRing.maximalIdeal 𝒪) ^ (n + 1))
            * ((⅟Pad).map π * (Mof σ).map π * Pad.map π) 1 1 := by
      have h1 : (Mof σ).map π * Pad.map π = Pad.map π * F'.map π := by
        rw [← Matrix.map_mul, hF'P, Matrix.map_mul]
      have h2 : (⅟Pad).map π * (Mof σ).map π * Pad.map π = F'.map π := by
        rw [Matrix.mul_assoc, h1, ← Matrix.mul_assoc, hUm'Um, Matrix.one_mul]
      rw [h2]
      constructor
      · rw [Matrix.map_apply, hF'10, map_zero]
      · rw [Matrix.map_apply, Matrix.map_apply, hF'ratio, map_mul, map_natCast]

    have hKcond : ∀ φ : Φ' D₀ D' θ x₀ →ₗ[𝒪] Rm 𝒪 (n + 1),
        (∀ τ ∈ P.inertiaSubgroupIn ℚ,
          (WCOTConjFam.conjFam (Pad.map π) ((⅟Pad).map π)
            (Λₗspec D₀ D' θ x₀ (n + 1)) φ τ) 1 0 = 0) →
        φ ∈ LinearMap.ker (LinearMap.lcomp 𝒪 (𝒪 ⧸ (IsLocalRing.maximalIdeal 𝒪) ^ (n + 1))
          (COT1.cotangentRelaxKer D₀ D' θ x₀).subtype) := by
      intro φ hu
      refine hK_of_row13a D₀ D' θ x₀ hx₀ hθ (n + 1) p q hp hq hpq P hP hθρ hθsurj hconj hur
        @Hdet @H1 @H2 φ ?_
      intro τ hτ
      obtain ⟨s, hs⟩ := hall (Mof τ) ⟨τ, hτ, rfl⟩
      have hsm := WCOTAdapt.shape_map π (Mof τ) Pad s hs
      have hshape : (⅟Pad).map π * (Mof τ).map π * Pad.map π
          = 1 + WCOTBridge.sl2M 0 (π s) 0 := by
        rw [Matrix.mul_assoc, hsm, ← Matrix.mul_assoc, hUm'Um, Matrix.one_mul]
        rfl
      have hadj : (Matrix.adjugate ((Mof τ).map π)
          * Λₗspec D₀ D' θ x₀ (n + 1) φ τ).trace = 0 := by
        have h0 := adjTrace_Λₗ_eq (x := xPrime D₀ D' θ x₀) (b := bD D')
          (G := AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (ρ := fun g => D'.ρ.ρ g)
          (M := 𝒪 ⧸ (IsLocalRing.maximalIdeal 𝒪) ^ (n + 1)) φ τ
        obtain ⟨c, hc⟩ := hdet1 τ hτ
        rw [hc, show cotOfEntry (xPrime D₀ D' θ x₀) (algebraMap 𝒪 D'.R c) = 0 from by
          rw [cotOfEntry_apply, δ_algebraMap, map_zero], map_zero, hFbarR τ] at h0
        exact h0.symm
      exact WCOTBridge.trace_eq_zero_of_adjugate_trace ((Mof τ).map π)
        (Λₗspec D₀ D' θ x₀ (n + 1) φ τ) (Pad.map π) ((⅟Pad).map π)
        hUmUm' hUm'Um (π s) hshape hadj (hu τ hτ)

    obtain ⟨γ, hγI, hgenγ⟩ := hgen (n + 1)
    exact Module.length_quotient_le_of_inertia_leibniz_family
      (P.inertiaSubgroupIn ℚ) σ γ hγI p q (n + 1) hp𝔪
      (fun τ hτ => hdivI (n + 1) τ hτ) hgenγ
      (fun g => (⅟Pad).map π * (Mof g).map π * Pad.map π)
      (fun g h => WCOTConjFam.conj_mul (Pad.map π) ((⅟Pad).map π) hUmUm'
        (fun g => (Mof g).map π) hFbRmul g h)
      (WCOTConjFam.conj_one (Pad.map π) ((⅟Pad).map π) hUm'Um
        (fun g => (Mof g).map π) hFbR1)
      hFI hFσc
      (WCOTConjFam.conjFam (Pad.map π) ((⅟Pad).map π) (Λₗspec D₀ D' θ x₀ (n + 1)))
      (fun φ g h => WCOTConjFam.conjFam_leibniz (Pad.map π) ((⅟Pad).map π) hUmUm'
        (fun g => (Mof g).map π) (Λₗspec D₀ D' θ x₀ (n + 1)) hLeib₀ φ g h)
      (LinearMap.ker (LinearMap.lcomp 𝒪 (𝒪 ⧸ (IsLocalRing.maximalIdeal 𝒪) ^ (n + 1))
        (COT1.cotangentRelaxKer D₀ D' θ x₀).subtype))
      hKcond

end WCOTLadderB
p2m_reactivate "P2MW.S_GaloisRep_DeformationRingData_length_level_quotient_le_of_isUnipotentOnInertiaAt.WCOTTameD"

open GaloisRep WCOTTameD
open scoped Pointwise

theorem solution
    {𝒪 : Type} [CommRing 𝒪] [IsDomain 𝒪] [IsDiscreteValuationRing 𝒪]
    [IsAdicComplete (IsLocalRing.maximalIdeal 𝒪) 𝒪]
    {ρbar : ResidualGaloisRep (IsLocalRing.ResidueField 𝒪)}
    {𝒟₀ 𝒟' : ∀ ⦃A : Type⦄ [CommRing A] [IsLocalRing A] [Algebra 𝒪 A], GaloisRepAdic A → Prop}
    (D₀ : GaloisRep.DeformationRingData 𝒪 ρbar 𝒟₀) (D' : GaloisRep.DeformationRingData 𝒪 ρbar 𝒟')
    (θ : D'.R →ₐ[𝒪] D₀.R) (x₀ : D₀.R →ₐ[𝒪] 𝒪)
    (hx₀ : IsLocalHom (x₀ : D₀.R →+* 𝒪)) (hθ : IsLocalHom (θ : D'.R →+* D₀.R))
    (hθρ : (D'.ρ.baseChangeAlong (θ : D'.R →+* D₀.R) hθ).IsEquiv D₀.ρ)
    (hθsurj : Function.Surjective (θ : D'.R →+* D₀.R))
    (p q : ℕ) (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q)
    (hp𝔪 : (p : 𝒪) ∈ IsLocalRing.maximalIdeal 𝒪)
    (P : ValuationSubring (AlgebraicClosure ℚ)) (hP : P.LiesOverPrime q)
    (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)
    (hconj : ∀ P' : ValuationSubring (AlgebraicClosure ℚ), P'.LiesOverPrime q →
      ∃ g : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ, g • P = P')
    (hx' : IsLocalHom (x₀.comp θ : D'.R →+* 𝒪))
    (hur : (D'.ρ.baseChangeAlong (x₀.comp θ : D'.R →+* 𝒪) hx').IsUnipotentOnInertiaAt q)
    (Hdet : ∀ {A : Type} [CommRing A] [IsLocalRing A] [Algebra 𝒪 A] (ρA : GaloisRepAdic A),
      𝒟' ρA → ρA.DetIsCyclotomic p)
    (H1 : ∀ {A : Type} [CommRing A] [IsLocalRing A] [Algebra 𝒪 A] (ρA : GaloisRepAdic A)
        {B : Type} [CommRing B] [IsLocalRing B] [Algebra 𝒪 B] (f : A →+* B) (hf : IsLocalHom f),
      𝒟' ρA → 𝒟' (ρA.baseChangeAlong f hf))
    (H2 : ∀ {A : Type} [CommRing A] [IsLocalRing A] [Algebra 𝒪 A] (ρA : GaloisRepAdic A),
      𝒟' ρA → ρA.IsUnipotentOnInertiaAt q → 𝒟₀ ρA)
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
    Module.length 𝒪 (𝒪 ⧸ Ideal.span {(q : 𝒪) ^ 2 - 1}) := by
  exact WCOTLadderB.lengthLevelB D₀ D' θ x₀ hx₀ hθ hθρ hθsurj p q hp hq hpq hp𝔪 P hP σ hconj hur Hdet H1 H2
    hdivI hgen n

end S_GaloisRep_DeformationRingData_length_level_quotient_le_of_isUnipotentOnInertiaAt
end P2MW
export P2MW.S_GaloisRep_DeformationRingData_length_level_quotient_le_of_isUnipotentOnInertiaAt (solution)
