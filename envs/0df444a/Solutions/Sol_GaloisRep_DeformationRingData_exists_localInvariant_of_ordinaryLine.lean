-- Prove2me | solution 1 for GaloisRep.DeformationRingData.exists_localInvariant_of_ordinaryLine
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:07.331093+00:00
-- url     : https://prove2.me/submissions/e44642d0-735d-5179-8d2c-8f8ea10453f7

import Mathlib
import Definitions.Def_GaloisRep_DeformationRingData
import Definitions.Def_GaloisRep_LocalConditions
import Definitions.Def_GaloisRep_Flat
import Definitions.Def_FLTPrelim_Ramification
import Mathlib.RingTheory.Ideal.Cotangent
import Mathlib.RingTheory.Length
import Mathlib.LinearAlgebra.BilinearMap
import Theorems.Thm_GaloisRep_DeformationRingData_comp_subtype_ker_mapCotangent_eq_zero_of_isOfType_lift
import Theorems.Thm_ValuationSubring_exists_kummer_decomposition_of_inertia_cocycle
import Theorems.Thm_ValuationSubring_sub_one_mul_sum_smul_eq_zero_of_corner_decomposition
import Theorems.Thm_IsDiscreteValuationRing_mem_maximalIdeal_pow_sub_of_mul_mem_of_not_mem
import Theorems.Thm_ValuationSubring_exists_eq_prime_pow_mul_of_forall_mem_inertiaSubgroupIn_apply_eq
import Theorems.Thm_GaloisRepAdic_isFlatAt_of_ordinary_of_unitKummer_decomposition
import Theorems.Thm_ValuationSubring_exists_isFrobeniusAt_of_liesOverPrime_algebraicClosure_rat
import Theorems.Thm_GaloisRepAdic_exists_level_forall_baseChangeAlong_apply_eq_one
import Theorems.Thm_ValuationSubring_exists_mem_inertiaSubgroupIn_apply_eq_pow_of_pow_prime_pow_eq_one
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_GaloisRep_DeformationRingData_exists_localInvariant_of_ordinaryLine
p2m_attr_erase "instance" "groupCohomology.Kummer.instMulDistribMulActionRootsOfUnity AlgebraicClosure.Rat.isGalois instIsScalarTowerTensorProduct_definitions"
p2m_attr_erase "simp" "groupCohomology.Kummer.coe_kummerCocycleRoots groupCohomology.Kummer.mem_powerSubgroup_iff groupCohomology.Kummer.val_smul_units groupCohomology.Kummer.kummerHom_apply groupCohomology.Kummer.coe_smul_rootsOfUnity closureCounit_apply genericFibreAlgHom_tmul tensorInclusion_closureComul coe_closureAntipode_apply tensorToGenericFibre_tmul tensorInclusion_tmul mem_flatClosure_iff"

set_option autoImplicit false

open scoped Pointwise

set_option autoImplicit false

open GaloisRep

namespace PRungCOT1

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

end PRungCOT1

open TrivSqZeroExt

local notation "tsze" => TrivSqZeroExt

namespace PRungD

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
    all_goals try rfl
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

end PRungD
p2m_reactivate "P2MW.S_GaloisRep_DeformationRingData_exists_localInvariant_of_ordinaryLine.PRungD"

open IsLocalRing TrivSqZeroExt

namespace PRungD

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

end PRungD
p2m_reactivate "P2MW.S_GaloisRep_DeformationRingData_exists_localInvariant_of_ordinaryLine.PRungD"

open TrivSqZeroExt

namespace PRungInvDict

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

end PRungInvDict
p2m_reactivate "P2MW.S_GaloisRep_DeformationRingData_exists_localInvariant_of_ordinaryLine.PRungD P2MW.S_GaloisRep_DeformationRingData_exists_localInvariant_of_ordinaryLine.PRungInvDict"

open GaloisRep
open scoped TensorProduct

namespace PRungXprime

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
p2m_reactivate "P2MW.S_GaloisRep_DeformationRingData_exists_localInvariant_of_ordinaryLine.PRungD P2MW.S_GaloisRep_DeformationRingData_exists_localInvariant_of_ordinaryLine.PRungInvDict"

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

end PRungXprime
p2m_reactivate "P2MW.S_GaloisRep_DeformationRingData_exists_localInvariant_of_ordinaryLine.PRungD P2MW.S_GaloisRep_DeformationRingData_exists_localInvariant_of_ordinaryLine.PRungInvDict"

namespace PRungD

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
p2m_reactivate "P2MW.S_GaloisRep_DeformationRingData_exists_localInvariant_of_ordinaryLine.PRungD P2MW.S_GaloisRep_DeformationRingData_exists_localInvariant_of_ordinaryLine.PRungInvDict"

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
  PRungD.Λₗ (xPrime D₀ D' θ x₀) (bD D') (G_ℚ) (fun g => D'.ρ.ρ g)

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
end hK
p2m_reactivate "P2MW.S_GaloisRep_DeformationRingData_exists_localInvariant_of_ordinaryLine.PRungD P2MW.S_GaloisRep_DeformationRingData_exists_localInvariant_of_ordinaryLine.PRungInvDict"

end PRungD
p2m_reactivate "P2MW.S_GaloisRep_DeformationRingData_exists_localInvariant_of_ordinaryLine.PRungD P2MW.S_GaloisRep_DeformationRingData_exists_localInvariant_of_ordinaryLine.PRungInvDict"

open Polynomial

namespace PRungFglue

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

end PRungFglue
p2m_reactivate "P2MW.S_GaloisRep_DeformationRingData_exists_localInvariant_of_ordinaryLine.PRungD P2MW.S_GaloisRep_DeformationRingData_exists_localInvariant_of_ordinaryLine.PRungInvDict"

namespace PRungFinal

open PRungD

variable {𝒪 : Type} [CommRing 𝒪] [IsDomain 𝒪] [IsDiscreteValuationRing 𝒪]
  [IsAdicComplete (IsLocalRing.maximalIdeal 𝒪) 𝒪]
  {ρbar : ResidualGaloisRep (IsLocalRing.ResidueField 𝒪)}
  {𝒟₀ 𝒟' : ∀ ⦃A : Type⦄ [CommRing A] [IsLocalRing A] [Algebra 𝒪 A], GaloisRepAdic A → Prop}
  (D₀ : DeformationRingData 𝒪 ρbar 𝒟₀) (D' : DeformationRingData 𝒪 ρbar 𝒟')
  (θ : D'.R →ₐ[𝒪] D₀.R) (x₀ : D₀.R →ₐ[𝒪] 𝒪)

set_option maxSynthPendingDepth 3 in

theorem ksub_le_ker_lcomp (m : ℕ) :
    Ksub D₀ D' θ x₀ m ≤ LinearMap.ker (LinearMap.lcomp 𝒪 (Rm 𝒪 m)
      (PRungCOT1.cotangentRelaxKer D₀ D' θ x₀).subtype) := by
  rintro φ ⟨φ₀, rfl⟩
  have h : LinearMap.lcomp 𝒪 (Rm 𝒪 m) (PRungCOT1.cotangentRelaxKer D₀ D' θ x₀).subtype
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
    (PRungCOT1.cotangentRelaxKer D₀ D' θ x₀).subtype)).mpr h

end PRungFinal
p2m_reactivate "P2MW.S_GaloisRep_DeformationRingData_exists_localInvariant_of_ordinaryLine.PRungD P2MW.S_GaloisRep_DeformationRingData_exists_localInvariant_of_ordinaryLine.PRungInvDict"

namespace PRungD

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
p2m_reactivate "P2MW.S_GaloisRep_DeformationRingData_exists_localInvariant_of_ordinaryLine.PRungD P2MW.S_GaloisRep_DeformationRingData_exists_localInvariant_of_ordinaryLine.PRungInvDict"

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
p2m_reactivate "P2MW.S_GaloisRep_DeformationRingData_exists_localInvariant_of_ordinaryLine.PRungD P2MW.S_GaloisRep_DeformationRingData_exists_localInvariant_of_ordinaryLine.PRungInvDict"

end PRungD
p2m_reactivate "P2MW.S_GaloisRep_DeformationRingData_exists_localInvariant_of_ordinaryLine.PRungD P2MW.S_GaloisRep_DeformationRingData_exists_localInvariant_of_ordinaryLine.PRungInvDict"

namespace PRungD

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
p2m_reactivate "P2MW.S_GaloisRep_DeformationRingData_exists_localInvariant_of_ordinaryLine.PRungD P2MW.S_GaloisRep_DeformationRingData_exists_localInvariant_of_ordinaryLine.PRungInvDict"

end PRungD
p2m_reactivate "P2MW.S_GaloisRep_DeformationRingData_exists_localInvariant_of_ordinaryLine.PRungD P2MW.S_GaloisRep_DeformationRingData_exists_localInvariant_of_ordinaryLine.PRungInvDict"

namespace PRungConjFam

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

end PRungConjFam
p2m_reactivate "P2MW.S_GaloisRep_DeformationRingData_exists_localInvariant_of_ordinaryLine.PRungD P2MW.S_GaloisRep_DeformationRingData_exists_localInvariant_of_ordinaryLine.PRungInvDict"

open Polynomial

namespace PRungAdapt

variable {R : Type} [CommRing R]

def sl2M (s t u : R) : Matrix (Fin 2) (Fin 2) R := Matrix.of ![![s, t], ![u, -s]]

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

end PRungAdapt
p2m_reactivate "P2MW.S_GaloisRep_DeformationRingData_exists_localInvariant_of_ordinaryLine.PRungD P2MW.S_GaloisRep_DeformationRingData_exists_localInvariant_of_ordinaryLine.PRungInvDict"

namespace PRungBridge

variable {R : Type} [CommRing R]

def sl2M (s t u : R) : Matrix (Fin 2) (Fin 2) R := Matrix.of ![![s, t], ![u, -s]]

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

end PRungBridge
p2m_reactivate "P2MW.S_GaloisRep_DeformationRingData_exists_localInvariant_of_ordinaryLine.PRungD P2MW.S_GaloisRep_DeformationRingData_exists_localInvariant_of_ordinaryLine.PRungInvDict"

namespace PRungPoint

variable {A : Type} [CommRing A] [IsLocalRing A]

theorem repr_one_eq_zero_of_mem_span (ρ : GaloisRepAdic A) (b : Module.Basis (Fin 2) A ρ.V)
    {v : ρ.V} (hv : v ∈ A ∙ b 0) : b.repr v 1 = 0 := by
  obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.mp hv
  rw [map_smul, Finsupp.smul_apply, b.repr_self, Finsupp.single_apply, if_neg (by decide), smul_zero]

theorem shapes (ρ : GaloisRepAdic A) (P : ValuationSubring (AlgebraicClosure ℚ))
    (b : Module.Basis (Fin 2) A ρ.V)
    (hLD : ∀ σ ∈ P.decompositionSubgroup ℚ, ∀ v ∈ A ∙ b 0, ρ.ρ σ v ∈ A ∙ b 0)
    (hLI : ∀ σ ∈ P.inertiaSubgroupIn ℚ, ∀ v : ρ.V, ρ.ρ σ v - v ∈ A ∙ b 0) :
    (∀ g ∈ P.decompositionSubgroup ℚ, LinearMap.toMatrix b b (ρ.ρ g) 1 0 = 0) ∧
    (∀ τ ∈ P.inertiaSubgroupIn ℚ,
      LinearMap.toMatrix b b (ρ.ρ τ) 1 0 = 0 ∧ LinearMap.toMatrix b b (ρ.ρ τ) 1 1 = 1) ∧
    (∀ (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (z : A), (∀ v : ρ.V, ρ.ρ σ v - z • v ∈ A ∙ b 0) →
      LinearMap.toMatrix b b (ρ.ρ σ) 1 0 = 0 ∧ LinearMap.toMatrix b b (ρ.ρ σ) 1 1 = z) := by
  refine ⟨fun g hg => ?_, fun τ hτ => ⟨?_, ?_⟩, fun σ z hz => ⟨?_, ?_⟩⟩
  · rw [LinearMap.toMatrix_apply]
    exact repr_one_eq_zero_of_mem_span ρ b (hLD g hg _ (Submodule.mem_span_singleton_self _))
  · rw [LinearMap.toMatrix_apply]
    have h := hLI τ hτ (b 0)
    have h' : ρ.ρ τ (b 0) ∈ A ∙ b 0 := by
      have := Submodule.add_mem _ h (Submodule.mem_span_singleton_self (b 0))
      rwa [sub_add_cancel] at this
    exact repr_one_eq_zero_of_mem_span ρ b h'
  · rw [LinearMap.toMatrix_apply]
    have h := repr_one_eq_zero_of_mem_span ρ b (hLI τ hτ (b 1))
    rw [map_sub, Finsupp.sub_apply, b.repr_self, Finsupp.single_apply, if_pos rfl, sub_eq_zero] at h
    exact h
  · rw [LinearMap.toMatrix_apply]
    have h := repr_one_eq_zero_of_mem_span ρ b (hz (b 0))
    rw [map_sub, map_smul, Finsupp.sub_apply, Finsupp.smul_apply, b.repr_self, Finsupp.single_apply,
      if_neg (by decide), smul_zero, sub_zero] at h
    exact h
  · rw [LinearMap.toMatrix_apply]
    have h := repr_one_eq_zero_of_mem_span ρ b (hz (b 1))
    rw [map_sub, map_smul, Finsupp.sub_apply, Finsupp.smul_apply, b.repr_self, Finsupp.single_apply,
      if_pos rfl, smul_eq_mul, mul_one, sub_eq_zero] at h
    exact h

end PRungPoint
p2m_reactivate "P2MW.S_GaloisRep_DeformationRingData_exists_localInvariant_of_ordinaryLine.PRungD P2MW.S_GaloisRep_DeformationRingData_exists_localInvariant_of_ordinaryLine.PRungInvDict"

namespace PRungPoint

variable {A : Type} [CommRing A] [IsLocalRing A]

omit [IsLocalRing A] in

theorem mem_span_symm_iff {V W : Type} [AddCommGroup V] [Module A V] [AddCommGroup W] [Module A W]
    (e : V ≃ₗ[A] W) (w : W) (v : V) : v ∈ A ∙ e.symm w ↔ e v ∈ A ∙ w := by
  constructor
  · intro hv
    obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.mp hv
    rw [map_smul, LinearEquiv.apply_symm_apply]
    exact Submodule.smul_mem _ a (Submodule.mem_span_singleton_self w)
  · intro hv
    obtain ⟨a, ha⟩ := Submodule.mem_span_singleton.mp hv
    have : v = a • e.symm w := by
      apply e.injective
      rw [map_smul, LinearEquiv.apply_symm_apply, ha]
    rw [this]
    exact Submodule.smul_mem _ a (Submodule.mem_span_singleton_self _)

theorem transport {ρ₁ ρ₂ : GaloisRepAdic A} (e : GaloisRepAdic.Equiv ρ₁ ρ₂)
    (P : ValuationSubring (AlgebraicClosure ℚ)) (b : Module.Basis (Fin 2) A ρ₂.V)
    (hLD : ∀ σ ∈ P.decompositionSubgroup ℚ, ∀ v ∈ A ∙ b 0, ρ₂.ρ σ v ∈ A ∙ b 0)
    (hLI : ∀ σ ∈ P.inertiaSubgroupIn ℚ, ∀ v : ρ₂.V, ρ₂.ρ σ v - v ∈ A ∙ b 0)
    (S : Set (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)) (α : A)
    (hα : ∀ σ ∈ S, ∀ v : ρ₂.V, ρ₂.ρ σ v - α • v ∈ A ∙ b 0) :
    (∀ σ ∈ P.decompositionSubgroup ℚ, ∀ v ∈ A ∙ (b.map e.toLinearEquiv.symm) 0,
        ρ₁.ρ σ v ∈ A ∙ (b.map e.toLinearEquiv.symm) 0) ∧
    (∀ σ ∈ P.inertiaSubgroupIn ℚ, ∀ v : ρ₁.V, ρ₁.ρ σ v - v ∈ A ∙ (b.map e.toLinearEquiv.symm) 0) ∧
    (∀ σ ∈ S, ∀ v : ρ₁.V, ρ₁.ρ σ v - α • v ∈ A ∙ (b.map e.toLinearEquiv.symm) 0) := by
  have hb0 : (b.map e.toLinearEquiv.symm) 0 = e.toLinearEquiv.symm (b 0) := by
    rw [Module.Basis.map_apply]
  rw [hb0]
  refine ⟨fun σ hσ v hv => ?_, fun σ hσ v => ?_, fun σ hσ v => ?_⟩
  · rw [mem_span_symm_iff] at hv ⊢
    rw [e.map_apply]
    exact hLD σ hσ _ hv
  · rw [mem_span_symm_iff, map_sub, e.map_apply]
    exact hLI σ hσ _
  · rw [mem_span_symm_iff, map_sub, map_smul, e.map_apply]
    exact hα σ hσ _

end PRungPoint
p2m_reactivate "P2MW.S_GaloisRep_DeformationRingData_exists_localInvariant_of_ordinaryLine.PRungD P2MW.S_GaloisRep_DeformationRingData_exists_localInvariant_of_ordinaryLine.PRungInvDict"

namespace PRungL2
namespace Setup

open PRungD GaloisRep

variable {𝒪 : Type} [CommRing 𝒪] [IsDomain 𝒪] [IsDiscreteValuationRing 𝒪]
  [IsAdicComplete (IsLocalRing.maximalIdeal 𝒪) 𝒪]
  {ρbar : ResidualGaloisRep (IsLocalRing.ResidueField 𝒪)}
  {𝒟₀ 𝒟' : ∀ ⦃A : Type⦄ [CommRing A] [IsLocalRing A] [Algebra 𝒪 A], GaloisRepAdic A → Prop}
  (D₀ : DeformationRingData 𝒪 ρbar 𝒟₀) (D' : DeformationRingData 𝒪 ρbar 𝒟')
  (θ : D'.R →ₐ[𝒪] D₀.R) (x₀ : D₀.R →ₐ[𝒪] 𝒪)
  (hx₀ : IsLocalHom (x₀ : D₀.R →+* 𝒪)) (hθ : IsLocalHom (θ : D'.R →+* D₀.R))

local notation "G_ℚ" => AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ

noncomputable def Mof (g : G_ℚ) : Matrix (Fin 2) (Fin 2) 𝒪 :=
  (LinearMap.toMatrix (bD D') (bD D') (D'.ρ.ρ g)).map (xPrime D₀ D' θ x₀ : D'.R →+* 𝒪)

theorem Mof_mul (g h : G_ℚ) : Mof D₀ D' θ x₀ (g * h) = Mof D₀ D' θ x₀ g * Mof D₀ D' θ x₀ h := by
  unfold Mof
  rw [map_mul, Module.End.mul_eq_comp, LinearMap.toMatrix_comp (bD D') (bD D') (bD D'), Matrix.map_mul]

theorem Mof_one : Mof D₀ D' θ x₀ 1 = 1 := by
  unfold Mof
  rw [map_one, Module.End.one_eq_id, LinearMap.toMatrix_id, Matrix.map_one _ (map_zero _) (map_one _)]

include hx₀ hθ in

theorem exists_adapted_frame
    (hθρ : (D'.ρ.baseChangeAlong (θ : D'.R →+* D₀.R) hθ).IsEquiv D₀.ρ)
    (P : ValuationSubring (AlgebraicClosure ℚ))
    (L : Submodule 𝒪 (D₀.ρ.baseChangeAlong (x₀ : D₀.R →+* 𝒪) hx₀).V)
    (hLb : ∃ b : Module.Basis (Fin 2) 𝒪 (D₀.ρ.baseChangeAlong (x₀ : D₀.R →+* 𝒪) hx₀).V, L = 𝒪 ∙ b 0)
    (hLD : ∀ σ ∈ P.decompositionSubgroup ℚ, ∀ v ∈ L,
      (D₀.ρ.baseChangeAlong (x₀ : D₀.R →+* 𝒪) hx₀).ρ σ v ∈ L)
    (hLI : ∀ σ ∈ P.inertiaSubgroupIn ℚ, ∀ v : (D₀.ρ.baseChangeAlong (x₀ : D₀.R →+* 𝒪) hx₀).V,
      (D₀.ρ.baseChangeAlong (x₀ : D₀.R →+* 𝒪) hx₀).ρ σ v - v ∈ L)
    (S : Set (G_ℚ)) (α : 𝒪)
    (hα : ∀ σ ∈ S, ∀ v : (D₀.ρ.baseChangeAlong (x₀ : D₀.R →+* 𝒪) hx₀).V,
        (D₀.ρ.baseChangeAlong (x₀ : D₀.R →+* 𝒪) hx₀).ρ σ v - α • v ∈ L) :
    ∃ U U' : Matrix (Fin 2) (Fin 2) 𝒪, U' * U = 1 ∧ U * U' = 1 ∧
      (∀ g ∈ P.decompositionSubgroup ℚ, (U' * Mof D₀ D' θ x₀ g * U) 1 0 = 0) ∧
      (∀ τ ∈ P.inertiaSubgroupIn ℚ,
        (U' * Mof D₀ D' θ x₀ τ * U) 1 0 = 0 ∧ (U' * Mof D₀ D' θ x₀ τ * U) 1 1 = 1) ∧
      (∀ σ ∈ S, (U' * Mof D₀ D' θ x₀ σ * U) 1 0 = 0 ∧ (U' * Mof D₀ D' θ x₀ σ * U) 1 1 = α) := by
  classical
  haveI hx' := isLocalHom_xPrime D₀ D' θ x₀ hx₀ hθ
  obtain ⟨e⟩ := PRungXprime.isEquiv_baseChangeAlong_comp D₀ D' θ hθ hθρ x₀ hx₀ hx'
  obtain ⟨b, rfl⟩ := hLb
  obtain ⟨TD, TI, Tα⟩ := PRungPoint.transport e P b hLD hLI S α hα
  set bad := b.map e.toLinearEquiv.symm with hbad
  obtain ⟨SD, SI, Sz⟩ := PRungPoint.shapes _ P bad TD TI
  letI : Algebra D'.R 𝒪 := (xPrime D₀ D' θ x₀ : D'.R →+* 𝒪).toAlgebra
  let c : Module.Basis (Fin 2) 𝒪 (D'.ρ.baseChangeAlong (xPrime D₀ D' θ x₀ : D'.R →+* 𝒪) hx').V :=
    (bD D').baseChange 𝒪
  have hdict : ∀ g : G_ℚ, LinearMap.toMatrix c c
      ((D'.ρ.baseChangeAlong (xPrime D₀ D' θ x₀ : D'.R →+* 𝒪) hx').ρ g) = Mof D₀ D' θ x₀ g :=
    fun g => toMatrix_baseChangeAlong_eq_map (xPrime D₀ D' θ x₀ : D'.R →+* 𝒪) hx' D'.ρ (bD D') g
  have hFad : ∀ g : G_ℚ, bad.toMatrix c * Mof D₀ D' θ x₀ g * c.toMatrix bad = LinearMap.toMatrix bad bad
      ((D'.ρ.baseChangeAlong (xPrime D₀ D' θ x₀ : D'.R →+* 𝒪) hx').ρ g) := by
    intro g
    have key := basis_toMatrix_mul_linearMap_toMatrix_mul_basis_toMatrix bad c bad c
      ((D'.ρ.baseChangeAlong (xPrime D₀ D' θ x₀ : D'.R →+* 𝒪) hx').ρ g)
    rw [hdict g] at key
    exact key
  refine ⟨c.toMatrix bad, bad.toMatrix c, Module.Basis.toMatrix_mul_toMatrix_flip _ _,
    Module.Basis.toMatrix_mul_toMatrix_flip _ _, ?_, ?_, ?_⟩
  · intro g hg
    rw [hFad]
    exact SD g hg
  · intro τ hτ
    rw [hFad]
    exact SI τ hτ
  · intro σ hσ
    rw [hFad]
    exact Sz σ α (Tα σ hσ)

end PRungL2.Setup
p2m_reactivate "P2MW.S_GaloisRep_DeformationRingData_exists_localInvariant_of_ordinaryLine.PRungD P2MW.S_GaloisRep_DeformationRingData_exists_localInvariant_of_ordinaryLine.PRungInvDict"
p2m_reactivate "P2MW.S_GaloisRep_DeformationRingData_exists_localInvariant_of_ordinaryLine.PRungD P2MW.S_GaloisRep_DeformationRingData_exists_localInvariant_of_ordinaryLine.PRungInvDict"

namespace PRungTsze
open TrivSqZeroExt

variable {R : Type} [CommRing R]

theorem map_inl_mul_map_inl (A B : Matrix (Fin 2) (Fin 2) R) :
    A.map (inl : R → TrivSqZeroExt R R) * B.map (inl : R → TrivSqZeroExt R R) =
      (A * B).map (inl : R → TrivSqZeroExt R R) :=
  (Matrix.map_mul (f := inlHom R R)).symm

theorem map_inl_mul_map_inr (A B : Matrix (Fin 2) (Fin 2) R) :
    A.map (inl : R → TrivSqZeroExt R R) * B.map (inr : R → TrivSqZeroExt R R) =
      (A * B).map (inr : R → TrivSqZeroExt R R) := by
  ext i j
  · rw [Matrix.map_apply, fst_inr, Matrix.mul_apply, fst_sum]
    simp [Matrix.map_apply, fst_mul]
  · rw [Matrix.map_apply, snd_inr, Matrix.mul_apply, snd_sum, Matrix.mul_apply]
    simp [Matrix.map_apply, snd_mul]
    ring

theorem map_inr_mul_map_inl (A B : Matrix (Fin 2) (Fin 2) R) :
    A.map (inr : R → TrivSqZeroExt R R) * B.map (inl : R → TrivSqZeroExt R R) =
      (A * B).map (inr : R → TrivSqZeroExt R R) := by
  ext i j
  · rw [Matrix.map_apply, fst_inr, Matrix.mul_apply, fst_sum]
    simp [Matrix.map_apply, fst_mul]
  · rw [Matrix.map_apply, snd_inr, Matrix.mul_apply, snd_sum, Matrix.mul_apply]
    simp [Matrix.map_apply, snd_mul, mul_comm]

theorem map_inr_mul_map_inr (A B : Matrix (Fin 2) (Fin 2) R) :
    A.map (inr : R → TrivSqZeroExt R R) * B.map (inr : R → TrivSqZeroExt R R) = 0 := by
  ext i j
  · rw [Matrix.mul_apply, fst_sum]
    simp [Matrix.map_apply]
  · rw [Matrix.mul_apply, snd_sum]
    simp [Matrix.map_apply]

theorem conj_pair_eq (U U' F L : Matrix (Fin 2) (Fin 2) R) :
    U'.map (inl : R → TrivSqZeroExt R R) * (F.map inl + L.map inr) * U.map inl =
      (U' * F * U).map (inl : R → TrivSqZeroExt R R) + (U' * L * U).map (inr : R → TrivSqZeroExt R R) := by
  rw [Matrix.mul_add, Matrix.add_mul, map_inl_mul_map_inl, map_inl_mul_map_inl, map_inl_mul_map_inr,
    map_inr_mul_map_inl]

end PRungTsze
p2m_reactivate "P2MW.S_GaloisRep_DeformationRingData_exists_localInvariant_of_ordinaryLine.PRungD P2MW.S_GaloisRep_DeformationRingData_exists_localInvariant_of_ordinaryLine.PRungInvDict"

namespace PRungTsze
open TrivSqZeroExt

variable {R : Type} [CommRing R]

local notation "inlM" => (Matrix.map · (inl : R → TrivSqZeroExt R R))
local notation "inrM" => (Matrix.map · (inr : R → TrivSqZeroExt R R))

theorem map_inl_mul_map_inl' (A B : Matrix (Fin 2) (Fin 2) R) :
    A.map (inl : R → TrivSqZeroExt R R) * B.map (inl : R → TrivSqZeroExt R R) =
      (A * B).map (inl : R → TrivSqZeroExt R R) :=
  (Matrix.map_mul (f := inlHom R R)).symm

theorem map_inl_mul_map_inr' (A B : Matrix (Fin 2) (Fin 2) R) :
    A.map (inl : R → TrivSqZeroExt R R) * B.map (inr : R → TrivSqZeroExt R R) =
      (A * B).map (inr : R → TrivSqZeroExt R R) := by
  ext i j
  · rw [Matrix.map_apply, fst_inr, Matrix.mul_apply, fst_sum]
    simp [Matrix.map_apply, fst_mul]
  · rw [Matrix.map_apply, snd_inr, Matrix.mul_apply, snd_sum, Matrix.mul_apply]
    simp [Matrix.map_apply, snd_mul]
    ring

theorem map_inr_mul_map_inl' (A B : Matrix (Fin 2) (Fin 2) R) :
    A.map (inr : R → TrivSqZeroExt R R) * B.map (inl : R → TrivSqZeroExt R R) =
      (A * B).map (inr : R → TrivSqZeroExt R R) := by
  ext i j
  · rw [Matrix.map_apply, fst_inr, Matrix.mul_apply, fst_sum]
    simp [Matrix.map_apply, fst_mul]
  · rw [Matrix.map_apply, snd_inr, Matrix.mul_apply, snd_sum, Matrix.mul_apply]
    simp [Matrix.map_apply, snd_mul, mul_comm]

theorem map_inr_mul_map_inr' (A B : Matrix (Fin 2) (Fin 2) R) :
    A.map (inr : R → TrivSqZeroExt R R) * B.map (inr : R → TrivSqZeroExt R R) = 0 := by
  ext i j
  · rw [Matrix.mul_apply, fst_sum]
    simp [Matrix.map_apply]
  · rw [Matrix.mul_apply, snd_sum]
    simp [Matrix.map_apply]

theorem map_inr_add (A B : Matrix (Fin 2) (Fin 2) R) :
    (A + B).map (inr : R → TrivSqZeroExt R R) = A.map inr + B.map inr :=
  Matrix.ext fun i j => (inrHom R R).map_add (A i j) (B i j)

theorem map_inr_sub (A B : Matrix (Fin 2) (Fin 2) R) :
    (A - B).map (inr : R → TrivSqZeroExt R R) = A.map inr - B.map inr :=
  Matrix.ext fun i j => (inrHom R R).map_sub (A i j) (B i j)

theorem map_inl_one : (1 : Matrix (Fin 2) (Fin 2) R).map (inl : R → TrivSqZeroExt R R) = 1 :=
  Matrix.map_one _ (inl_zero R) (inl_one R)

theorem one_add_map_inr_mul_one_sub (N : Matrix (Fin 2) (Fin 2) R) :
    (1 + N.map (inr : R → TrivSqZeroExt R R)) * (1 - N.map inr) = 1 := by
  rw [Matrix.add_mul, Matrix.mul_sub, Matrix.mul_sub, Matrix.one_mul, Matrix.one_mul, Matrix.mul_one,
    map_inr_mul_map_inr', sub_zero]
  abel

theorem one_sub_map_inr_mul_one_add (N : Matrix (Fin 2) (Fin 2) R) :
    (1 - N.map (inr : R → TrivSqZeroExt R R)) * (1 + N.map inr) = 1 := by
  rw [Matrix.sub_mul, Matrix.mul_add, Matrix.mul_add, Matrix.one_mul, Matrix.one_mul, Matrix.mul_one,
    map_inr_mul_map_inr', add_zero]
  abel

theorem retriang_conj_eq (Ubar Ubar' Mm L N : Matrix (Fin 2) (Fin 2) R) :
    ((1 - N.map (inr : R → TrivSqZeroExt R R)) * Ubar'.map inl) *
        (Mm.map inl + L.map inr) * (Ubar.map inl * (1 + N.map inr)) =
      (Ubar' * Mm * Ubar).map (inl : R → TrivSqZeroExt R R) +
        (Ubar' * L * Ubar + (Ubar' * Mm * Ubar) * N - N * (Ubar' * Mm * Ubar)).map inr := by
  set F := Ubar' * Mm * Ubar with hF
  set Λ := Ubar' * L * Ubar with hΛ
  have hmid : Ubar'.map (inl : R → TrivSqZeroExt R R) * (Mm.map inl + L.map inr) * Ubar.map inl =
      F.map inl + Λ.map inr := by
    rw [Matrix.mul_add, Matrix.add_mul, map_inl_mul_map_inl', map_inl_mul_map_inl', map_inl_mul_map_inr',
      map_inr_mul_map_inl']
  calc ((1 - N.map (inr : R → TrivSqZeroExt R R)) * Ubar'.map inl) *
        (Mm.map inl + L.map inr) * (Ubar.map inl * (1 + N.map inr))
      = (1 - N.map inr) * (Ubar'.map (inl : R → TrivSqZeroExt R R) * (Mm.map inl + L.map inr) * Ubar.map inl) *
          (1 + N.map inr) := by simp only [Matrix.mul_assoc]
    _ = (1 - N.map inr) * (F.map inl + Λ.map inr) * (1 + N.map inr) := by rw [hmid]
    _ = F.map inl + (Λ + F * N - N * F).map inr := by
        rw [Matrix.sub_mul, Matrix.one_mul, Matrix.mul_add (N.map inr), map_inr_mul_map_inl',
          map_inr_mul_map_inr', add_zero, Matrix.mul_add, Matrix.mul_one, Matrix.sub_mul,
          Matrix.add_mul, map_inl_mul_map_inr', map_inr_mul_map_inr', add_zero, map_inr_mul_map_inr',
          sub_zero, map_inr_sub, map_inr_add]
        abel

theorem W_mul_W'_eq_one (Ubar Ubar' N : Matrix (Fin 2) (Fin 2) R) (h : Ubar * Ubar' = 1) :
    (Ubar.map (inl : R → TrivSqZeroExt R R) * (1 + N.map inr)) * ((1 - N.map inr) * Ubar'.map inl) = 1 := by
  calc (Ubar.map (inl : R → TrivSqZeroExt R R) * (1 + N.map inr)) * ((1 - N.map inr) * Ubar'.map inl)
      = Ubar.map inl * ((1 + N.map (inr : R → TrivSqZeroExt R R)) * (1 - N.map inr)) * Ubar'.map inl := by
        simp only [Matrix.mul_assoc]
    _ = 1 := by rw [one_add_map_inr_mul_one_sub, Matrix.mul_one, map_inl_mul_map_inl', h, map_inl_one]

theorem W'_mul_W_eq_one (Ubar Ubar' N : Matrix (Fin 2) (Fin 2) R) (h : Ubar' * Ubar = 1) :
    ((1 - N.map (inr : R → TrivSqZeroExt R R)) * Ubar'.map inl) * (Ubar.map inl * (1 + N.map inr)) = 1 := by
  calc ((1 - N.map (inr : R → TrivSqZeroExt R R)) * Ubar'.map inl) * (Ubar.map inl * (1 + N.map inr))
      = (1 - N.map inr) * (Ubar'.map (inl : R → TrivSqZeroExt R R) * Ubar.map inl) * (1 + N.map inr) := by
        simp only [Matrix.mul_assoc]
    _ = 1 := by rw [map_inl_mul_map_inl', h, map_inl_one, Matrix.mul_one, one_sub_map_inr_mul_one_add]

end PRungTsze
p2m_reactivate "P2MW.S_GaloisRep_DeformationRingData_exists_localInvariant_of_ordinaryLine.PRungD P2MW.S_GaloisRep_DeformationRingData_exists_localInvariant_of_ordinaryLine.PRungInvDict"

namespace PRungConjFam

variable {S : Type} [CommRing S] {G : Type}

theorem mul_of_conj_eq [Mul G] (W W' : Matrix (Fin 2) (Fin 2) S) (hWW' : W * W' = 1)
    (M F : G → Matrix (Fin 2) (Fin 2) S) (hM : ∀ g h, M (g * h) = M g * M h)
    (hF : ∀ g, F g = W' * M g * W) (g h : G) : F (g * h) = F g * F h := by
  rw [hF, hF, hF, hM]
  calc W' * (M g * M h) * W = W' * (M g * (W * W') * M h) * W := by rw [hWW', Matrix.mul_one]
    _ = W' * M g * W * (W' * M h * W) := by simp only [Matrix.mul_assoc]

theorem one_of_conj_eq [One G] (W W' : Matrix (Fin 2) (Fin 2) S) (hW'W : W' * W = 1)
    (M F : G → Matrix (Fin 2) (Fin 2) S) (hM1 : M 1 = 1) (hF : ∀ g, F g = W' * M g * W) : F 1 = 1 := by
  rw [hF, hM1, Matrix.mul_one, hW'W]

end PRungConjFam
p2m_reactivate "P2MW.S_GaloisRep_DeformationRingData_exists_localInvariant_of_ordinaryLine.PRungD P2MW.S_GaloisRep_DeformationRingData_exists_localInvariant_of_ordinaryLine.PRungInvDict"

namespace PRungEntries

variable {G A : Type} [Group G] [CommRing A]
  (F : G → Matrix (Fin 2) (Fin 2) A)
  (hmul : ∀ g h, F (g * h) = F g * F h) (hone : F 1 = 1)
  (D : Subgroup G) (hD : ∀ g ∈ D, F g 1 0 = 0)

include hmul in
theorem entry00_mul (hD : ∀ g ∈ D, F g 1 0 = 0) :
    ∀ g ∈ D, ∀ h ∈ D, F (g * h) 0 0 = F g 0 0 * F h 0 0 := by
  intro g _ h hh
  rw [hmul, Matrix.mul_apply, Fin.sum_univ_two, hD h hh, mul_zero, add_zero]

include hmul in
theorem entry11_mul (hD : ∀ g ∈ D, F g 1 0 = 0) :
    ∀ g ∈ D, ∀ h ∈ D, F (g * h) 1 1 = F g 1 1 * F h 1 1 := by
  intro g hg h _
  rw [hmul, Matrix.mul_apply, Fin.sum_univ_two, hD g hg, zero_mul, zero_add]

include hmul in
theorem entry01_mul :
    ∀ g ∈ D, ∀ h ∈ D, F (g * h) 0 1 = F g 0 0 * F h 0 1 + F g 0 1 * F h 1 1 := by
  intro g _ h _
  rw [hmul, Matrix.mul_apply, Fin.sum_univ_two]

include hmul hone in
theorem isUnit_det (g : G) : IsUnit (F g).det := by
  have h : (F g).det * (F g⁻¹).det = 1 := by
    rw [← Matrix.det_mul, ← hmul, mul_inv_cancel, hone, Matrix.det_one]
  exact IsUnit.of_mul_eq_one _ h

theorem det_eq_entry_mul (hD : ∀ g ∈ D, F g 1 0 = 0) (g : G) (hg : g ∈ D) :
    (F g).det = F g 0 0 * F g 1 1 := by
  rw [Matrix.det_fin_two, hD g hg, mul_zero, sub_zero]

include hmul hone in
theorem isUnit_entry00 (hD : ∀ g ∈ D, F g 1 0 = 0) : ∀ g ∈ D, IsUnit (F g 0 0) := by
  intro g hg
  have h := isUnit_det F hmul hone g
  rw [det_eq_entry_mul F D hD g hg] at h
  exact (IsUnit.mul_iff.mp h).1

include hmul hone in
theorem isUnit_entry11 (hD : ∀ g ∈ D, F g 1 0 = 0) : ∀ g ∈ D, IsUnit (F g 1 1) := by
  intro g hg
  have h := isUnit_det F hmul hone g
  rw [det_eq_entry_mul F D hD g hg] at h
  exact (IsUnit.mul_iff.mp h).2

theorem entry00_mul_entry11_eq_of_det_eq (hD : ∀ g ∈ D, F g 1 0 = 0) (g : G) (hg : g ∈ D)
    (e : A) (hdet : (F g).det = e) : F g 0 0 * F g 1 1 = e := by
  rw [← det_eq_entry_mul F D hD g hg, hdet]

theorem entry11_eq_one_of (I : Set G) (hI : ∀ τ ∈ I, F τ 1 1 = 1) : ∀ τ ∈ I, F τ 1 1 = 1 := hI

end PRungEntries
p2m_reactivate "P2MW.S_GaloisRep_DeformationRingData_exists_localInvariant_of_ordinaryLine.PRungD P2MW.S_GaloisRep_DeformationRingData_exists_localInvariant_of_ordinaryLine.PRungInvDict"

example {G A : Type} [Group G] [CommRing A] (F : G → Matrix (Fin 2) (Fin 2) A)
    (hmul : ∀ g h, F (g * h) = F g * F h) (hone : F 1 = 1)
    (D I : Subgroup G) (hID : I ≤ D) (hD : ∀ g ∈ D, F g 1 0 = 0) (hI : ∀ τ ∈ I, F τ 1 1 = 1) :
    (∀ g ∈ D, ∀ h ∈ D, (fun x => F x 0 0) (g * h) = (fun x => F x 0 0) g * (fun x => F x 0 0) h) ∧
    (∀ g ∈ D, ∀ h ∈ D, (fun x => F x 1 1) (g * h) = (fun x => F x 1 1) g * (fun x => F x 1 1) h) ∧
    (∀ g ∈ D, ∀ h ∈ D, (fun x => F x 0 1) (g * h) =
      (fun x => F x 0 0) g * (fun x => F x 0 1) h + (fun x => F x 0 1) g * (fun x => F x 1 1) h) ∧
    (∀ g ∈ D, IsUnit ((fun x => F x 0 0) g)) ∧ (∀ g ∈ D, IsUnit ((fun x => F x 1 1) g)) ∧
    (∀ τ ∈ I, (fun x => F x 1 1) τ = 1) :=
  ⟨PRungEntries.entry00_mul F hmul D hD, PRungEntries.entry11_mul F hmul D hD,
    PRungEntries.entry01_mul F hmul D, PRungEntries.isUnit_entry00 F hmul hone D hD,
    PRungEntries.isUnit_entry11 F hmul hone D hD, hI⟩

namespace PRungL2
namespace Obj

open PRungD GaloisRep PRungL2.Setup

variable {𝒪 : Type} [CommRing 𝒪] [IsDomain 𝒪] [IsDiscreteValuationRing 𝒪]
  [IsAdicComplete (IsLocalRing.maximalIdeal 𝒪) 𝒪]
  {ρbar : ResidualGaloisRep (IsLocalRing.ResidueField 𝒪)}
  {𝒟₀ 𝒟' : ∀ ⦃A : Type⦄ [CommRing A] [IsLocalRing A] [Algebra 𝒪 A], GaloisRepAdic A → Prop}
  (D₀ : DeformationRingData 𝒪 ρbar 𝒟₀) (D' : DeformationRingData 𝒪 ρbar 𝒟')
  (θ : D'.R →ₐ[𝒪] D₀.R) (x₀ : D₀.R →ₐ[𝒪] 𝒪)
  (U U' : Matrix (Fin 2) (Fin 2) 𝒪) (m : ℕ) [NeZero m]

local notation "G_ℚ" => AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ

noncomputable def Fad (g : G_ℚ) : Matrix (Fin 2) (Fin 2) 𝒪 := U' * Mof D₀ D' θ x₀ g * U

noncomputable def Fadm (g : G_ℚ) : Matrix (Fin 2) (Fin 2) (Rm 𝒪 m) :=
  (Fad D₀ D' θ x₀ U U' g).map (algebraMap 𝒪 (Rm 𝒪 m))

noncomputable def Lam : (Φ' D₀ D' θ x₀ →ₗ[𝒪] Rm 𝒪 m) →ₗ[𝒪] (G_ℚ → Matrix (Fin 2) (Fin 2) (Rm 𝒪 m)) :=
  PRungConjFam.conjFam (U.map (algebraMap 𝒪 (Rm 𝒪 m))) (U'.map (algebraMap 𝒪 (Rm 𝒪 m)))
    (Λₗspec D₀ D' θ x₀ m)

variable (g₀ : G_ℚ)

noncomputable def w₁ : (Φ' D₀ D' θ x₀ →ₗ[𝒪] Rm 𝒪 m) →ₗ[𝒪] Rm 𝒪 m where
  toFun φ := Lam D₀ D' θ x₀ U U' m φ g₀ 1 0 *
    Ring.inverse (Fadm D₀ D' θ x₀ U U' m g₀ 0 0 - Fadm D₀ D' θ x₀ U U' m g₀ 1 1)
  map_add' φ ψ := by rw [map_add, Pi.add_apply, Matrix.add_apply, add_mul]
  map_smul' c φ := by
    rw [map_smul, Pi.smul_apply, Matrix.smul_apply, RingHom.id_apply, smul_mul_assoc]

noncomputable def Nmat (φ : Φ' D₀ D' θ x₀ →ₗ[𝒪] Rm 𝒪 m) : Matrix (Fin 2) (Fin 2) (Rm 𝒪 m) :=
  Matrix.of ![![0, 0], ![w₁ D₀ D' θ x₀ U U' m g₀ φ, 0]]

noncomputable def LamT (φ : Φ' D₀ D' θ x₀ →ₗ[𝒪] Rm 𝒪 m) (g : G_ℚ) : Matrix (Fin 2) (Fin 2) (Rm 𝒪 m) :=
  Lam D₀ D' θ x₀ U U' m φ g + Fadm D₀ D' θ x₀ U U' m g * Nmat D₀ D' θ x₀ U U' m g₀ φ -
    Nmat D₀ D' θ x₀ U U' m g₀ φ * Fadm D₀ D' θ x₀ U U' m g

noncomputable def Ftil (φ : Φ' D₀ D' θ x₀ →ₗ[𝒪] Rm 𝒪 m) (g : G_ℚ) : Matrix (Fin 2) (Fin 2) (Am 𝒪 m) :=
  (Fadm D₀ D' θ x₀ U U' m g).map (TrivSqZeroExt.inl) + (LamT D₀ D' θ x₀ U U' m g₀ φ g).map (TrivSqZeroExt.inr)

end PRungL2.Obj
p2m_reactivate "P2MW.S_GaloisRep_DeformationRingData_exists_localInvariant_of_ordinaryLine.PRungD P2MW.S_GaloisRep_DeformationRingData_exists_localInvariant_of_ordinaryLine.PRungInvDict"
p2m_reactivate "P2MW.S_GaloisRep_DeformationRingData_exists_localInvariant_of_ordinaryLine.PRungD P2MW.S_GaloisRep_DeformationRingData_exists_localInvariant_of_ordinaryLine.PRungInvDict"

namespace PRungL2
namespace Obj

open PRungD GaloisRep PRungL2.Setup

variable {𝒪 : Type} [CommRing 𝒪] [IsDomain 𝒪] [IsDiscreteValuationRing 𝒪]
  [IsAdicComplete (IsLocalRing.maximalIdeal 𝒪) 𝒪]
  {ρbar : ResidualGaloisRep (IsLocalRing.ResidueField 𝒪)}
  {𝒟₀ 𝒟' : ∀ ⦃A : Type⦄ [CommRing A] [IsLocalRing A] [Algebra 𝒪 A], GaloisRepAdic A → Prop}
  (D₀ : DeformationRingData 𝒪 ρbar 𝒟₀) (D' : DeformationRingData 𝒪 ρbar 𝒟')
  (θ : D'.R →ₐ[𝒪] D₀.R) (x₀ : D₀.R →ₐ[𝒪] 𝒪)
  (hx₀ : IsLocalHom (x₀ : D₀.R →+* 𝒪)) (hθ : IsLocalHom (θ : D'.R →+* D₀.R))
  (m : ℕ) [NeZero m] (φ : Φ' D₀ D' θ x₀ →ₗ[𝒪] Rm 𝒪 m)

theorem toMatrix_dualNumber_eq :
    haveI := isLocalHom_xPrime D₀ D' θ x₀ hx₀ hθ
    letI : Algebra D'.R (Am 𝒪 m) :=
      (xOfCotangentHom (xPrime D₀ D' θ x₀) φ : D'.R →+* Am 𝒪 m).toAlgebra
    ∀ g : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ,
      LinearMap.toMatrix ((bD D').baseChange (Am 𝒪 m)) ((bD D').baseChange (Am 𝒪 m))
        ((D'.ρ.baseChangeAlong (xOfCotangentHom (xPrime D₀ D' θ x₀) φ : D'.R →+* Am 𝒪 m)
          (isLocalHom_xOfCotangentHom (xPrime D₀ D' θ x₀) φ)).ρ g) =
      ((Mof D₀ D' θ x₀ g).map (algebraMap 𝒪 (Rm 𝒪 m))).map TrivSqZeroExt.inl +
        (Λₗspec D₀ D' θ x₀ m φ g).map TrivSqZeroExt.inr := by
  haveI hx' := isLocalHom_xPrime D₀ D' θ x₀ hx₀ hθ
  letI : Algebra D'.R (Am 𝒪 m) :=
    (xOfCotangentHom (xPrime D₀ D' θ x₀) φ : D'.R →+* Am 𝒪 m).toAlgebra
  intro g
  refine (toMatrix_baseChangeAlong_eq_map
    (xOfCotangentHom (xPrime D₀ D' θ x₀) φ : D'.R →+* Am 𝒪 m) _ D'.ρ (bD D') g).trans ?_
  ext i j
  · simp only [Matrix.map_apply, Matrix.add_apply, TrivSqZeroExt.fst_add, TrivSqZeroExt.fst_inl,
      TrivSqZeroExt.fst_inr, add_zero, Mof]
    rfl
  · simp only [Matrix.map_apply, Matrix.add_apply, TrivSqZeroExt.snd_add, TrivSqZeroExt.snd_inl,
      TrivSqZeroExt.snd_inr, zero_add]
    rfl

end PRungL2.Obj
p2m_reactivate "P2MW.S_GaloisRep_DeformationRingData_exists_localInvariant_of_ordinaryLine.PRungD P2MW.S_GaloisRep_DeformationRingData_exists_localInvariant_of_ordinaryLine.PRungInvDict"
p2m_reactivate "P2MW.S_GaloisRep_DeformationRingData_exists_localInvariant_of_ordinaryLine.PRungD P2MW.S_GaloisRep_DeformationRingData_exists_localInvariant_of_ordinaryLine.PRungInvDict"

namespace PRungL2
namespace Obj

open PRungD GaloisRep PRungL2.Setup TrivSqZeroExt

variable {𝒪 : Type} [CommRing 𝒪] [IsDomain 𝒪] [IsDiscreteValuationRing 𝒪]
  [IsAdicComplete (IsLocalRing.maximalIdeal 𝒪) 𝒪]
  {ρbar : ResidualGaloisRep (IsLocalRing.ResidueField 𝒪)}
  {𝒟₀ 𝒟' : ∀ ⦃A : Type⦄ [CommRing A] [IsLocalRing A] [Algebra 𝒪 A], GaloisRepAdic A → Prop}
  (D₀ : DeformationRingData 𝒪 ρbar 𝒟₀) (D' : DeformationRingData 𝒪 ρbar 𝒟')
  (θ : D'.R →ₐ[𝒪] D₀.R) (x₀ : D₀.R →ₐ[𝒪] 𝒪)
  (U U' : Matrix (Fin 2) (Fin 2) 𝒪) (m : ℕ) [NeZero m]
  (g₀ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)
  (φ : Φ' D₀ D' θ x₀ →ₗ[𝒪] Rm 𝒪 m)

local notation "G_ℚ" => AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ

noncomputable abbrev Ubar : Matrix (Fin 2) (Fin 2) (Rm 𝒪 m) := U.map (algebraMap 𝒪 (Rm 𝒪 m))

noncomputable abbrev Ubar' : Matrix (Fin 2) (Fin 2) (Rm 𝒪 m) := U'.map (algebraMap 𝒪 (Rm 𝒪 m))

noncomputable def Mtil (g : G_ℚ) : Matrix (Fin 2) (Fin 2) (Am 𝒪 m) :=
  ((Mof D₀ D' θ x₀ g).map (algebraMap 𝒪 (Rm 𝒪 m))).map inl + (Λₗspec D₀ D' θ x₀ m φ g).map inr

noncomputable def Wmat : Matrix (Fin 2) (Fin 2) (Am 𝒪 m) :=
  (Ubar U m).map inl * (1 + (Nmat D₀ D' θ x₀ U U' m g₀ φ).map inr)

noncomputable def Wmat' : Matrix (Fin 2) (Fin 2) (Am 𝒪 m) :=
  (1 - (Nmat D₀ D' θ x₀ U U' m g₀ φ).map inr) * (Ubar' U' m).map inl

theorem Fadm_eq (g : G_ℚ) :
    Fadm D₀ D' θ x₀ U U' m g = Ubar' U' m * (Mof D₀ D' θ x₀ g).map (algebraMap 𝒪 (Rm 𝒪 m)) * Ubar U m := by
  simp only [Fadm, Fad, Matrix.map_mul]

theorem Lam_eq (g : G_ℚ) :
    Lam D₀ D' θ x₀ U U' m φ g = Ubar' U' m * Λₗspec D₀ D' θ x₀ m φ g * Ubar U m := rfl

theorem Ftil_eq_conj (g : G_ℚ) :
    Ftil D₀ D' θ x₀ U U' m g₀ φ g =
      Wmat' D₀ D' θ x₀ U U' m g₀ φ * Mtil D₀ D' θ x₀ m φ g * Wmat D₀ D' θ x₀ U U' m g₀ φ := by
  rw [Wmat', Mtil, Wmat, PRungTsze.retriang_conj_eq, Ftil, LamT, Fadm_eq, Lam_eq]

theorem Wmat_mul_Wmat' (hUU' : U * U' = 1) :
    Wmat D₀ D' θ x₀ U U' m g₀ φ * Wmat' D₀ D' θ x₀ U U' m g₀ φ = 1 := by
  refine PRungTsze.W_mul_W'_eq_one _ _ _ ?_
  rw [← Matrix.map_mul, hUU', Matrix.map_one _ (map_zero _) (map_one _)]

theorem Wmat'_mul_Wmat (hUU' : U * U' = 1) :
    Wmat' D₀ D' θ x₀ U U' m g₀ φ * Wmat D₀ D' θ x₀ U U' m g₀ φ = 1 := by
  refine PRungTsze.W'_mul_W_eq_one _ _ _ ?_
  rw [← Matrix.map_mul, mul_eq_one_comm.mp hUU', Matrix.map_one _ (map_zero _) (map_one _)]

theorem Ftil_mul (hUU' : U * U' = 1)
    (hM : ∀ g h : G_ℚ, Mtil D₀ D' θ x₀ m φ (g * h) = Mtil D₀ D' θ x₀ m φ g * Mtil D₀ D' θ x₀ m φ h)
    (g h : G_ℚ) :
    Ftil D₀ D' θ x₀ U U' m g₀ φ (g * h) = Ftil D₀ D' θ x₀ U U' m g₀ φ g * Ftil D₀ D' θ x₀ U U' m g₀ φ h :=
  PRungConjFam.mul_of_conj_eq _ _ (Wmat_mul_Wmat' D₀ D' θ x₀ U U' m g₀ φ hUU') (Mtil D₀ D' θ x₀ m φ) _ hM
    (Ftil_eq_conj D₀ D' θ x₀ U U' m g₀ φ) g h

theorem Ftil_one (hUU' : U * U' = 1) (hM1 : Mtil D₀ D' θ x₀ m φ 1 = 1) :
    Ftil D₀ D' θ x₀ U U' m g₀ φ 1 = 1 :=
  PRungConjFam.one_of_conj_eq _ _ (Wmat'_mul_Wmat D₀ D' θ x₀ U U' m g₀ φ hUU') (Mtil D₀ D' θ x₀ m φ) _ hM1
    (Ftil_eq_conj D₀ D' θ x₀ U U' m g₀ φ)

theorem Mtil_mul (hx₀ : IsLocalHom (x₀ : D₀.R →+* 𝒪)) (hθ : IsLocalHom (θ : D'.R →+* D₀.R)) :
    (∀ g h : G_ℚ, Mtil D₀ D' θ x₀ m φ (g * h) = Mtil D₀ D' θ x₀ m φ g * Mtil D₀ D' θ x₀ m φ h) ∧
      Mtil D₀ D' θ x₀ m φ 1 = 1 := by
  haveI hx' := isLocalHom_xPrime D₀ D' θ x₀ hx₀ hθ
  have hd := PRungL2.Obj.toMatrix_dualNumber_eq D₀ D' θ x₀ hx₀ hθ m φ
  letI : Algebra D'.R (Am 𝒪 m) :=
    (xOfCotangentHom (xPrime D₀ D' θ x₀) φ : D'.R →+* Am 𝒪 m).toAlgebra
  set ρt : GaloisRepAdic (Am 𝒪 m) := D'.ρ.baseChangeAlong
    (xOfCotangentHom (xPrime D₀ D' θ x₀) φ : D'.R →+* Am 𝒪 m)
    (isLocalHom_xOfCotangentHom (xPrime D₀ D' θ x₀) φ) with hρt
  let c : Module.Basis (Fin 2) (Am 𝒪 m) ρt.V := (bD D').baseChange (Am 𝒪 m)
  have hdict : ∀ g : G_ℚ, LinearMap.toMatrix c c (ρt.ρ g) = Mtil D₀ D' θ x₀ m φ g := hd
  refine ⟨fun g h => ?_, ?_⟩
  · rw [← hdict, ← hdict, ← hdict, map_mul, Module.End.mul_eq_comp, LinearMap.toMatrix_comp c c c]
  · rw [← hdict, map_one, Module.End.one_eq_id, LinearMap.toMatrix_id]

end PRungL2.Obj
p2m_reactivate "P2MW.S_GaloisRep_DeformationRingData_exists_localInvariant_of_ordinaryLine.PRungD P2MW.S_GaloisRep_DeformationRingData_exists_localInvariant_of_ordinaryLine.PRungInvDict"
p2m_reactivate "P2MW.S_GaloisRep_DeformationRingData_exists_localInvariant_of_ordinaryLine.PRungD P2MW.S_GaloisRep_DeformationRingData_exists_localInvariant_of_ordinaryLine.PRungInvDict"

namespace PRungD

variable (𝒪 : Type) [CommRing 𝒪] [IsDomain 𝒪] [IsDiscreteValuationRing 𝒪] (m : ℕ) [NeZero m]

theorem natCast_pow_eq_zero_Rm (p : ℕ) (hp : (p : 𝒪) ∈ IsLocalRing.maximalIdeal 𝒪) :
    ((p : ℕ) : Rm 𝒪 m) ^ m = 0 := by
  rw [← map_natCast (algebraMap 𝒪 (Rm 𝒪 m)) p, ← map_pow, Ideal.Quotient.algebraMap_eq,
    Ideal.Quotient.eq_zero_iff_mem]
  exact Ideal.pow_mem_pow hp m

theorem natCast_pow_eq_zero_Rm_of_le (p : ℕ) (hp : (p : 𝒪) ∈ IsLocalRing.maximalIdeal 𝒪) {N : ℕ}
    (hN : m ≤ N) : ((p : ℕ) : Rm 𝒪 m) ^ N = 0 := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hN
  rw [pow_add, natCast_pow_eq_zero_Rm 𝒪 m p hp, zero_mul]

theorem natCast_pow_eq_zero_Am_of_le (p : ℕ) (hp : (p : 𝒪) ∈ IsLocalRing.maximalIdeal 𝒪) {N : ℕ}
    (hN : m ≤ N) : ((p : ℕ) : Am 𝒪 m) ^ N = 0 := by
  rw [← map_natCast (algebraMap (Rm 𝒪 m) (Am 𝒪 m)) p, ← map_pow, natCast_pow_eq_zero_Rm_of_le 𝒪 m p hp hN,
    map_zero]

theorem natCast_pow_eq_zero_Am (p : ℕ) (hp : (p : 𝒪) ∈ IsLocalRing.maximalIdeal 𝒪) :
    ((p : ℕ) : Am 𝒪 m) ^ m = 0 :=
  natCast_pow_eq_zero_Am_of_le 𝒪 m p hp le_rfl

theorem finite_Rm [Finite (IsLocalRing.ResidueField 𝒪)] : Finite (Rm 𝒪 m) := by
  haveI : Finite (𝒪 ⧸ IsLocalRing.maximalIdeal 𝒪) := ‹Finite (IsLocalRing.ResidueField 𝒪)›
  exact Ideal.finite_quotient_pow (IsNoetherian.noetherian (IsLocalRing.maximalIdeal 𝒪)) m

theorem finite_Am [Finite (IsLocalRing.ResidueField 𝒪)] : Finite (Am 𝒪 m) := by
  haveI := finite_Rm 𝒪 m
  exact inferInstanceAs (Finite (Rm 𝒪 m × Rm 𝒪 m))

end PRungD
p2m_reactivate "P2MW.S_GaloisRep_DeformationRingData_exists_localInvariant_of_ordinaryLine.PRungD P2MW.S_GaloisRep_DeformationRingData_exists_localInvariant_of_ordinaryLine.PRungInvDict"

namespace PRungL2
namespace Obj

open PRungD GaloisRep PRungL2.Setup TrivSqZeroExt

variable {𝒪 : Type} [CommRing 𝒪] [IsDomain 𝒪] [IsDiscreteValuationRing 𝒪]
  [IsAdicComplete (IsLocalRing.maximalIdeal 𝒪) 𝒪]
  {ρbar : ResidualGaloisRep (IsLocalRing.ResidueField 𝒪)}
  {𝒟₀ 𝒟' : ∀ ⦃A : Type⦄ [CommRing A] [IsLocalRing A] [Algebra 𝒪 A], GaloisRepAdic A → Prop}
  (D₀ : DeformationRingData 𝒪 ρbar 𝒟₀) (D' : DeformationRingData 𝒪 ρbar 𝒟')
  (θ : D'.R →ₐ[𝒪] D₀.R) (x₀ : D₀.R →ₐ[𝒪] 𝒪)
  (hx₀ : IsLocalHom (x₀ : D₀.R →+* 𝒪)) (hθ : IsLocalHom (θ : D'.R →+* D₀.R))
  (U U' : Matrix (Fin 2) (Fin 2) 𝒪) (m : ℕ) [NeZero m]
  (g₀ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)
  (φ : Φ' D₀ D' θ x₀ →ₗ[𝒪] Rm 𝒪 m)

local notation "G_ℚ" => AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ

theorem det_Ftil_eq_det_Mtil (hUU' : U * U' = 1) (g : G_ℚ) :
    (Ftil D₀ D' θ x₀ U U' m g₀ φ g).det = (Mtil D₀ D' θ x₀ m φ g).det := by
  rw [Ftil_eq_conj, Matrix.det_mul, Matrix.det_mul, mul_right_comm, ← Matrix.det_mul, Wmat'_mul_Wmat _ _ _ _ _ _ _ _ _ hUU',
    Matrix.det_one, one_mul]

include hx₀ hθ in

theorem det_Mtil_eq (g : G_ℚ) :
    haveI := isLocalHom_xPrime D₀ D' θ x₀ hx₀ hθ
    (Mtil D₀ D' θ x₀ m φ g).det =
      LinearMap.det ((D'.ρ.baseChangeAlong (xOfCotangentHom (xPrime D₀ D' θ x₀) φ : D'.R →+* Am 𝒪 m)
        (isLocalHom_xOfCotangentHom (xPrime D₀ D' θ x₀) φ)).ρ g) := by
  haveI hx' := isLocalHom_xPrime D₀ D' θ x₀ hx₀ hθ
  have hd := PRungL2.Obj.toMatrix_dualNumber_eq D₀ D' θ x₀ hx₀ hθ m φ
  letI : Algebra D'.R (Am 𝒪 m) :=
    (xOfCotangentHom (xPrime D₀ D' θ x₀) φ : D'.R →+* Am 𝒪 m).toAlgebra
  set ρt : GaloisRepAdic (Am 𝒪 m) := D'.ρ.baseChangeAlong
    (xOfCotangentHom (xPrime D₀ D' θ x₀) φ : D'.R →+* Am 𝒪 m)
    (isLocalHom_xOfCotangentHom (xPrime D₀ D' θ x₀) φ) with hρt
  let c : Module.Basis (Fin 2) (Am 𝒪 m) ρt.V := (bD D').baseChange (Am 𝒪 m)
  have hdict : ∀ g : G_ℚ, LinearMap.toMatrix c c (ρt.ρ g) = Mtil D₀ D' θ x₀ m φ g := hd
  rw [← hdict g, LinearMap.det_toMatrix]

theorem forall_pow_eq_one_apply_eq_pow {p N : ℕ} [NeZero p] (ζ : AlgebraicClosure ℚ)
    (hζ : IsPrimitiveRoot ζ (p ^ N)) (g : G_ℚ) (e : ℕ) (hg : g ζ = ζ ^ e) :
    ∀ μ : AlgebraicClosure ℚ, μ ^ p ^ N = 1 → g μ = μ ^ e := by
  intro μ hμ
  obtain ⟨k, -, rfl⟩ := hζ.eq_pow_of_pow_eq_one hμ
  rw [map_pow, hg, ← pow_mul, ← pow_mul, mul_comm]

include hx₀ hθ in

theorem det_Ftil_eq_natCast (hUU' : U * U' = 1) {p N : ℕ} [NeZero p]
    (hdet : haveI := isLocalHom_xPrime D₀ D' θ x₀ hx₀ hθ
      (D'.ρ.baseChangeAlong (xOfCotangentHom (xPrime D₀ D' θ x₀) φ : D'.R →+* Am 𝒪 m)
        (isLocalHom_xOfCotangentHom (xPrime D₀ D' θ x₀) φ)).DetIsCyclotomic p)
    (hpN : ((p : ℕ) : Am 𝒪 m) ^ N = 0) (ζ : AlgebraicClosure ℚ) (hζ : IsPrimitiveRoot ζ (p ^ N))
    (g : G_ℚ) (e : ℕ) (hg : g ζ = ζ ^ e) :
    (Ftil D₀ D' θ x₀ U U' m g₀ φ g).det = (e : Am 𝒪 m) := by
  have h3 := hdet.2 N g e (forall_pow_eq_one_apply_eq_pow ζ hζ g e hg)
  rw [Nat.cast_pow, hpN, Ideal.span_singleton_eq_bot.mpr rfl, Ideal.mem_bot, sub_eq_zero] at h3
  rw [det_Ftil_eq_det_Mtil _ _ _ _ _ _ _ _ _ hUU', det_Mtil_eq D₀ D' θ x₀ hx₀ hθ m φ g]
  exact h3

include hx₀ hθ in

theorem entries_det_eq_natCast (hUU' : U * U' = 1) {p N : ℕ} [NeZero p]
    (hdet : haveI := isLocalHom_xPrime D₀ D' θ x₀ hx₀ hθ
      (D'.ρ.baseChangeAlong (xOfCotangentHom (xPrime D₀ D' θ x₀) φ : D'.R →+* Am 𝒪 m)
        (isLocalHom_xOfCotangentHom (xPrime D₀ D' θ x₀) φ)).DetIsCyclotomic p)
    (hpN : ((p : ℕ) : Am 𝒪 m) ^ N = 0) (ζ : AlgebraicClosure ℚ) (hζ : IsPrimitiveRoot ζ (p ^ N))
    (g : G_ℚ) (e : ℕ) (hg : g ζ = ζ ^ e) :
    Ftil D₀ D' θ x₀ U U' m g₀ φ g 0 0 * Ftil D₀ D' θ x₀ U U' m g₀ φ g 1 1 -
      Ftil D₀ D' θ x₀ U U' m g₀ φ g 0 1 * Ftil D₀ D' θ x₀ U U' m g₀ φ g 1 0 = (e : Am 𝒪 m) := by
  rw [← Matrix.det_fin_two]
  exact det_Ftil_eq_natCast D₀ D' θ x₀ hx₀ hθ U U' m g₀ φ hUU' hdet hpN ζ hζ g e hg

end PRungL2.Obj
p2m_reactivate "P2MW.S_GaloisRep_DeformationRingData_exists_localInvariant_of_ordinaryLine.PRungD P2MW.S_GaloisRep_DeformationRingData_exists_localInvariant_of_ordinaryLine.PRungInvDict"
p2m_reactivate "P2MW.S_GaloisRep_DeformationRingData_exists_localInvariant_of_ordinaryLine.PRungD P2MW.S_GaloisRep_DeformationRingData_exists_localInvariant_of_ordinaryLine.PRungInvDict"

namespace PRungL2
namespace Obj

open PRungD GaloisRep PRungL2.Setup

variable {𝒪 : Type} [CommRing 𝒪] [IsDomain 𝒪] [IsDiscreteValuationRing 𝒪]
  [IsAdicComplete (IsLocalRing.maximalIdeal 𝒪) 𝒪]
  {ρbar : ResidualGaloisRep (IsLocalRing.ResidueField 𝒪)}
  {𝒟₀ 𝒟' : ∀ ⦃A : Type⦄ [CommRing A] [IsLocalRing A] [Algebra 𝒪 A], GaloisRepAdic A → Prop}
  (D₀ : DeformationRingData 𝒪 ρbar 𝒟₀) (D' : DeformationRingData 𝒪 ρbar 𝒟')
  (θ : D'.R →ₐ[𝒪] D₀.R) (x₀ : D₀.R →ₐ[𝒪] 𝒪)
  (U U' : Matrix (Fin 2) (Fin 2) 𝒪)

local notation "G_ℚ" => AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ

theorem Fad_mul (hUU' : U * U' = 1) (g h : G_ℚ) :
    Fad D₀ D' θ x₀ U U' (g * h) = Fad D₀ D' θ x₀ U U' g * Fad D₀ D' θ x₀ U U' h :=
  PRungConjFam.conj_mul U U' hUU' (Mof D₀ D' θ x₀) (Mof_mul D₀ D' θ x₀) g h

theorem Fad_one (hU'U : U' * U = 1) : Fad D₀ D' θ x₀ U U' 1 = 1 :=
  PRungConjFam.conj_one U U' hU'U (Mof D₀ D' θ x₀) (Mof_one D₀ D' θ x₀)

theorem Fadm_mul (m : ℕ) (hUU' : U * U' = 1) (g h : G_ℚ) :
    Fadm D₀ D' θ x₀ U U' m (g * h) = Fadm D₀ D' θ x₀ U U' m g * Fadm D₀ D' θ x₀ U U' m h := by
  simp only [Fadm, Fad_mul D₀ D' θ x₀ U U' hUU', Matrix.map_mul]

theorem Fadm_one (m : ℕ) (hU'U : U' * U = 1) : Fadm D₀ D' θ x₀ U U' m 1 = 1 := by
  simp only [Fadm, Fad_one D₀ D' θ x₀ U U' hU'U, Matrix.map_one _ (map_zero _) (map_one _)]

noncomputable def red (𝒪 : Type) [CommRing 𝒪] [IsDomain 𝒪] [IsDiscreteValuationRing 𝒪] {m M : ℕ} (hmM : m ≤ M) :
    Rm 𝒪 M →+* Rm 𝒪 m :=
  Ideal.Quotient.lift _ (Ideal.Quotient.mk _) fun a ha =>
    Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.pow_le_pow_right hmM ha)

theorem red_mk {m M : ℕ} (hmM : m ≤ M) (a : 𝒪) :
    red 𝒪 hmM (Ideal.Quotient.mk _ a) = Ideal.Quotient.mk _ a := rfl

noncomputable def evφ {m M : ℕ} (hmM : m ≤ M) (φ : Φ' D₀ D' θ x₀ →ₗ[𝒪] Rm 𝒪 m) :
    (Rm 𝒪 M × ((Φ' D₀ D' θ x₀ →ₗ[𝒪] Rm 𝒪 m) →ₗ[𝒪] Rm 𝒪 m)) →+ Am 𝒪 m where
  toFun x := TrivSqZeroExt.inl (red 𝒪 hmM x.1) + TrivSqZeroExt.inr (x.2 φ)
  map_zero' := by
    simp only [Prod.fst_zero, Prod.snd_zero, map_zero, LinearMap.zero_apply, TrivSqZeroExt.inl_zero,
      TrivSqZeroExt.inr_zero, add_zero]
  map_add' x y := by
    simp only [Prod.fst_add, Prod.snd_add, map_add, LinearMap.add_apply, TrivSqZeroExt.inl_add,
      TrivSqZeroExt.inr_add]
    abel

theorem evφ_apply {m M : ℕ} (hmM : m ≤ M) (φ : Φ' D₀ D' θ x₀ →ₗ[𝒪] Rm 𝒪 m)
    (x : Rm 𝒪 M × ((Φ' D₀ D' θ x₀ →ₗ[𝒪] Rm 𝒪 m) →ₗ[𝒪] Rm 𝒪 m)) :
    evφ D₀ D' θ x₀ hmM φ x = TrivSqZeroExt.inl (red 𝒪 hmM x.1) + TrivSqZeroExt.inr (x.2 φ) := rfl

theorem fst_evφ {m M : ℕ} (hmM : m ≤ M) (φ : Φ' D₀ D' θ x₀ →ₗ[𝒪] Rm 𝒪 m)
    (x : Rm 𝒪 M × ((Φ' D₀ D' θ x₀ →ₗ[𝒪] Rm 𝒪 m) →ₗ[𝒪] Rm 𝒪 m)) :
    (evφ D₀ D' θ x₀ hmM φ x).fst = red 𝒪 hmM x.1 := by
  rw [evφ_apply, TrivSqZeroExt.fst_add, TrivSqZeroExt.fst_inl, TrivSqZeroExt.fst_inr, add_zero]

theorem snd_evφ {m M : ℕ} (hmM : m ≤ M) (φ : Φ' D₀ D' θ x₀ →ₗ[𝒪] Rm 𝒪 m)
    (x : Rm 𝒪 M × ((Φ' D₀ D' θ x₀ →ₗ[𝒪] Rm 𝒪 m) →ₗ[𝒪] Rm 𝒪 m)) :
    (evφ D₀ D' θ x₀ hmM φ x).snd = x.2 φ := by
  rw [evφ_apply, TrivSqZeroExt.snd_add, TrivSqZeroExt.snd_inl, TrivSqZeroExt.snd_inr, zero_add]

end PRungL2.Obj
p2m_reactivate "P2MW.S_GaloisRep_DeformationRingData_exists_localInvariant_of_ordinaryLine.PRungD P2MW.S_GaloisRep_DeformationRingData_exists_localInvariant_of_ordinaryLine.PRungInvDict"
p2m_reactivate "P2MW.S_GaloisRep_DeformationRingData_exists_localInvariant_of_ordinaryLine.PRungD P2MW.S_GaloisRep_DeformationRingData_exists_localInvariant_of_ordinaryLine.PRungInvDict"

namespace PRungNmat
variable {R : Type} [CommRing R]

theorem entry10 (F L : Matrix (Fin 2) (Fin 2) R) (w : R) :
    (L + F * Matrix.of ![![0, 0], ![w, 0]] - Matrix.of ![![0, 0], ![w, 0]] * F) 1 0 =
      L 1 0 + w * (F 1 1 - F 0 0) := by
  simp [Matrix.add_apply, Matrix.sub_apply, Matrix.mul_apply, Fin.sum_univ_two, Matrix.vecMul, dotProduct]
  ring

theorem entry11 (F L : Matrix (Fin 2) (Fin 2) R) (w : R) :
    (L + F * Matrix.of ![![0, 0], ![w, 0]] - Matrix.of ![![0, 0], ![w, 0]] * F) 1 1 =
      L 1 1 - w * F 0 1 := by
  simp [Matrix.add_apply, Matrix.sub_apply, Matrix.mul_apply, Fin.sum_univ_two, Matrix.vecMul, dotProduct]
  try ring

theorem entry01 (F L : Matrix (Fin 2) (Fin 2) R) (w : R) :
    (L + F * Matrix.of ![![0, 0], ![w, 0]] - Matrix.of ![![0, 0], ![w, 0]] * F) 0 1 = L 0 1 := by
  simp [Matrix.add_apply, Matrix.sub_apply, Matrix.mul_apply, Fin.sum_univ_two, Matrix.vecMul, dotProduct]

theorem entry00 (F L : Matrix (Fin 2) (Fin 2) R) (w : R) :
    (L + F * Matrix.of ![![0, 0], ![w, 0]] - Matrix.of ![![0, 0], ![w, 0]] * F) 0 0 =
      L 0 0 + F 0 1 * w := by
  simp [Matrix.add_apply, Matrix.sub_apply, Matrix.mul_apply, Fin.sum_univ_two, Matrix.vecMul, dotProduct]
  try ring

end PRungNmat
p2m_reactivate "P2MW.S_GaloisRep_DeformationRingData_exists_localInvariant_of_ordinaryLine.PRungD P2MW.S_GaloisRep_DeformationRingData_exists_localInvariant_of_ordinaryLine.PRungInvDict"

namespace PRungL2
namespace Obj

open PRungD GaloisRep PRungL2.Setup TrivSqZeroExt

variable {𝒪 : Type} [CommRing 𝒪] [IsDomain 𝒪] [IsDiscreteValuationRing 𝒪]
  [IsAdicComplete (IsLocalRing.maximalIdeal 𝒪) 𝒪]
  {ρbar : ResidualGaloisRep (IsLocalRing.ResidueField 𝒪)}
  {𝒟₀ 𝒟' : ∀ ⦃A : Type⦄ [CommRing A] [IsLocalRing A] [Algebra 𝒪 A], GaloisRepAdic A → Prop}
  (D₀ : DeformationRingData 𝒪 ρbar 𝒟₀) (D' : DeformationRingData 𝒪 ρbar 𝒟')
  (θ : D'.R →ₐ[𝒪] D₀.R) (x₀ : D₀.R →ₐ[𝒪] 𝒪)
  (U U' : Matrix (Fin 2) (Fin 2) 𝒪) (m : ℕ) [NeZero m]
  (g₀ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)
  (φ : Φ' D₀ D' θ x₀ →ₗ[𝒪] Rm 𝒪 m)

local notation "G_ℚ" => AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ

theorem LamT_apply_10 (g : G_ℚ) : LamT D₀ D' θ x₀ U U' m g₀ φ g 1 0 =
    Lam D₀ D' θ x₀ U U' m φ g 1 0 +
      w₁ D₀ D' θ x₀ U U' m g₀ φ * (Fadm D₀ D' θ x₀ U U' m g 1 1 - Fadm D₀ D' θ x₀ U U' m g 0 0) :=
  PRungNmat.entry10 _ _ _

theorem LamT_apply_11 (g : G_ℚ) : LamT D₀ D' θ x₀ U U' m g₀ φ g 1 1 =
    Lam D₀ D' θ x₀ U U' m φ g 1 1 - w₁ D₀ D' θ x₀ U U' m g₀ φ * Fadm D₀ D' θ x₀ U U' m g 0 1 :=
  PRungNmat.entry11 _ _ _

theorem LamT_apply_01 (g : G_ℚ) : LamT D₀ D' θ x₀ U U' m g₀ φ g 0 1 = Lam D₀ D' θ x₀ U U' m φ g 0 1 :=
  PRungNmat.entry01 _ _ _

theorem Ftil_apply (g : G_ℚ) (i j : Fin 2) : Ftil D₀ D' θ x₀ U U' m g₀ φ g i j =
    inl (Fadm D₀ D' θ x₀ U U' m g i j) + inr (LamT D₀ D' θ x₀ U U' m g₀ φ g i j) := by
  rw [Ftil, Matrix.add_apply, Matrix.map_apply, Matrix.map_apply]

theorem Fadm_apply (g : G_ℚ) (i j : Fin 2) :
    Fadm D₀ D' θ x₀ U U' m g i j = algebraMap 𝒪 (Rm 𝒪 m) (Fad D₀ D' θ x₀ U U' g i j) := rfl

theorem Ftil_10_eq_zero (g : G_ℚ) (h10 : Fad D₀ D' θ x₀ U U' g 1 0 = 0)
    (hkey : Lam D₀ D' θ x₀ U U' m φ g 1 0 +
      w₁ D₀ D' θ x₀ U U' m g₀ φ * (Fadm D₀ D' θ x₀ U U' m g 1 1 - Fadm D₀ D' θ x₀ U U' m g 0 0) = 0) :
    Ftil D₀ D' θ x₀ U U' m g₀ φ g 1 0 = 0 := by
  rw [Ftil_apply, LamT_apply_10, hkey, Fadm_apply, h10, map_zero, inl_zero, inr_zero, add_zero]

theorem Ftil_11_eq_one (g : G_ℚ) (h11 : Fad D₀ D' θ x₀ U U' g 1 1 = 1)
    (hkey : Lam D₀ D' θ x₀ U U' m φ g 1 1 - w₁ D₀ D' θ x₀ U U' m g₀ φ * Fadm D₀ D' θ x₀ U U' m g 0 1 = 0) :
    Ftil D₀ D' θ x₀ U U' m g₀ φ g 1 1 = 1 := by
  rw [Ftil_apply, LamT_apply_11, hkey, Fadm_apply, h11, map_one, inr_zero, add_zero]
  rfl

theorem Ftil_apply_01 (g : G_ℚ) : Ftil D₀ D' θ x₀ U U' m g₀ φ g 0 1 =
    inl (Fadm D₀ D' θ x₀ U U' m g 0 1) + inr (Lam D₀ D' θ x₀ U U' m φ g 0 1) := by
  rw [Ftil_apply, LamT_apply_01]

theorem fst_Ftil_apply (g : G_ℚ) (i j : Fin 2) :
    (Ftil D₀ D' θ x₀ U U' m g₀ φ g i j).fst = Fadm D₀ D' θ x₀ U U' m g i j := by
  rw [Ftil_apply, fst_add, fst_inl, fst_inr, add_zero]

theorem snd_Ftil_apply (g : G_ℚ) (i j : Fin 2) :
    (Ftil D₀ D' θ x₀ U U' m g₀ φ g i j).snd = LamT D₀ D' θ x₀ U U' m g₀ φ g i j := by
  rw [Ftil_apply, snd_add, snd_inl, snd_inr, zero_add]

end PRungL2.Obj
p2m_reactivate "P2MW.S_GaloisRep_DeformationRingData_exists_localInvariant_of_ordinaryLine.PRungD P2MW.S_GaloisRep_DeformationRingData_exists_localInvariant_of_ordinaryLine.PRungInvDict"
p2m_reactivate "P2MW.S_GaloisRep_DeformationRingData_exists_localInvariant_of_ordinaryLine.PRungD P2MW.S_GaloisRep_DeformationRingData_exists_localInvariant_of_ordinaryLine.PRungInvDict"

namespace PRungL2
namespace Obj

open PRungD GaloisRep PRungL2.Setup

variable {𝒪 : Type} [CommRing 𝒪] [IsDomain 𝒪] [IsDiscreteValuationRing 𝒪]
  [IsAdicComplete (IsLocalRing.maximalIdeal 𝒪) 𝒪]
  {ρbar : ResidualGaloisRep (IsLocalRing.ResidueField 𝒪)}
  {𝒟₀ 𝒟' : ∀ ⦃A : Type⦄ [CommRing A] [IsLocalRing A] [Algebra 𝒪 A], GaloisRepAdic A → Prop}
  (D₀ : DeformationRingData 𝒪 ρbar 𝒟₀) (D' : DeformationRingData 𝒪 ρbar 𝒟')
  (θ : D'.R →ₐ[𝒪] D₀.R) (x₀ : D₀.R →ₐ[𝒪] 𝒪)
  (hx₀ : IsLocalHom (x₀ : D₀.R →+* 𝒪)) (hθ : IsLocalHom (θ : D'.R →+* D₀.R))
  (U U' : Matrix (Fin 2) (Fin 2) 𝒪)

local notation "G_ℚ" => AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ

theorem det_Fad_eq_det_Mof (hUU' : U * U' = 1) (g : G_ℚ) :
    (Fad D₀ D' θ x₀ U U' g).det = (Mof D₀ D' θ x₀ g).det := by
  rw [Fad, Matrix.det_mul, Matrix.det_mul, mul_right_comm, ← Matrix.det_mul, mul_eq_one_comm.mp hUU',
    Matrix.det_one, one_mul]

include hx₀ hθ in

theorem det_Mof_eq (g : G_ℚ) :
    (Mof D₀ D' θ x₀ g).det =
      LinearMap.det ((D'.ρ.baseChangeAlong (xPrime D₀ D' θ x₀ : D'.R →+* 𝒪)
        (isLocalHom_xPrime D₀ D' θ x₀ hx₀ hθ)).ρ g) := by
  letI : Algebra D'.R 𝒪 := (xPrime D₀ D' θ x₀ : D'.R →+* 𝒪).toAlgebra
  set ρx : GaloisRepAdic 𝒪 := D'.ρ.baseChangeAlong (xPrime D₀ D' θ x₀ : D'.R →+* 𝒪)
    (isLocalHom_xPrime D₀ D' θ x₀ hx₀ hθ) with hρx
  let c : Module.Basis (Fin 2) 𝒪 ρx.V := (bD D').baseChange 𝒪
  have h : LinearMap.toMatrix c c (ρx.ρ g) =
      (LinearMap.toMatrix (bD D') (bD D') (D'.ρ.ρ g)).map (xPrime D₀ D' θ x₀ : D'.R →+* 𝒪) :=
    toMatrix_baseChangeAlong_eq_map (xPrime D₀ D' θ x₀ : D'.R →+* 𝒪)
      (isLocalHom_xPrime D₀ D' θ x₀ hx₀ hθ) D'.ρ (bD D') g
  rw [Mof, ← h, LinearMap.det_toMatrix]

include hx₀ hθ in

theorem det_Fad_sub_mem_span (hUU' : U * U' = 1) {p : ℕ}
    (hdetP : (D'.ρ.baseChangeAlong (xPrime D₀ D' θ x₀ : D'.R →+* 𝒪)
        (isLocalHom_xPrime D₀ D' θ x₀ hx₀ hθ)).DetIsCyclotomic p)
    (g : G_ℚ) (n a : ℕ) (hμ : ∀ μ : AlgebraicClosure ℚ, μ ^ p ^ n = 1 → g μ = μ ^ a) :
    (Fad D₀ D' θ x₀ U U' g).det - (a : 𝒪) ∈ Ideal.span {((p ^ n : ℕ) : 𝒪)} := by
  rw [det_Fad_eq_det_Mof D₀ D' θ x₀ U U' hUU', det_Mof_eq D₀ D' θ x₀ hx₀ hθ]
  exact hdetP.2 n g a hμ

end PRungL2.Obj
p2m_reactivate "P2MW.S_GaloisRep_DeformationRingData_exists_localInvariant_of_ordinaryLine.PRungD P2MW.S_GaloisRep_DeformationRingData_exists_localInvariant_of_ordinaryLine.PRungInvDict"
p2m_reactivate "P2MW.S_GaloisRep_DeformationRingData_exists_localInvariant_of_ordinaryLine.PRungD P2MW.S_GaloisRep_DeformationRingData_exists_localInvariant_of_ordinaryLine.PRungInvDict"

namespace PRungBasisVec

variable {R V : Type} [CommRing R] [AddCommGroup V] [Module R V]

theorem apply_basis_eq (b : Module.Basis (Fin 2) R V) (f : Module.End R V) (T : Matrix (Fin 2) (Fin 2) R)
    (hT : LinearMap.toMatrix b b f = T) (j : Fin 2) : f (b j) = T 0 j • b 0 + T 1 j • b 1 := by
  have h := (b.sum_repr (f (b j))).symm
  rw [Fin.sum_univ_two] at h
  rw [← hT, LinearMap.toMatrix_apply, LinearMap.toMatrix_apply]
  exact h

theorem apply_zero_mem_span (b : Module.Basis (Fin 2) R V) (f : Module.End R V) (T : Matrix (Fin 2) (Fin 2) R)
    (hT : LinearMap.toMatrix b b f = T) (h10 : T 1 0 = 0) : f (b 0) ∈ R ∙ b 0 := by
  rw [apply_basis_eq b f T hT 0, h10, zero_smul, add_zero]
  exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self _)

theorem apply_one_sub_eq (b : Module.Basis (Fin 2) R V) (f : Module.End R V) (T : Matrix (Fin 2) (Fin 2) R)
    (hT : LinearMap.toMatrix b b f = T) (h11 : T 1 1 = 1) : f (b 1) - b 1 = T 0 1 • b 0 := by
  rw [apply_basis_eq b f T hT 1, h11, one_smul, add_sub_cancel_right]

theorem sub_mem_span (b : Module.Basis (Fin 2) R V) (f : Module.End R V) (T : Matrix (Fin 2) (Fin 2) R)
    (hT : LinearMap.toMatrix b b f = T) (h10 : T 1 0 = 0) (h11 : T 1 1 = 1) (v : V) : f v - v ∈ R ∙ b 0 := by
  have key : ∀ j : Fin 2, f (b j) - b j ∈ R ∙ b 0 := by
    refine Fin.forall_fin_two.mpr ⟨?_, ?_⟩
    · exact Submodule.sub_mem _ (apply_zero_mem_span b f T hT h10) (Submodule.mem_span_singleton_self _)
    · rw [apply_one_sub_eq b f T hT h11]
      exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self _)
  have hv := b.sum_repr v
  rw [Fin.sum_univ_two] at hv
  rw [← hv, map_add, map_smul, map_smul, add_sub_add_comm, ← smul_sub, ← smul_sub]
  exact Submodule.add_mem _ (Submodule.smul_mem _ _ (key 0)) (Submodule.smul_mem _ _ (key 1))

end PRungBasisVec
p2m_reactivate "P2MW.S_GaloisRep_DeformationRingData_exists_localInvariant_of_ordinaryLine.PRungD P2MW.S_GaloisRep_DeformationRingData_exists_localInvariant_of_ordinaryLine.PRungInvDict"

namespace PRungL2
namespace Obj

open PRungD GaloisRep PRungL2.Setup TrivSqZeroExt

variable {𝒪 : Type} [CommRing 𝒪] [IsDomain 𝒪] [IsDiscreteValuationRing 𝒪]
  [IsAdicComplete (IsLocalRing.maximalIdeal 𝒪) 𝒪]
  {ρbar : ResidualGaloisRep (IsLocalRing.ResidueField 𝒪)}
  {𝒟₀ 𝒟' : ∀ ⦃A : Type⦄ [CommRing A] [IsLocalRing A] [Algebra 𝒪 A], GaloisRepAdic A → Prop}
  (D₀ : DeformationRingData 𝒪 ρbar 𝒟₀) (D' : DeformationRingData 𝒪 ρbar 𝒟')
  (θ : D'.R →ₐ[𝒪] D₀.R) (x₀ : D₀.R →ₐ[𝒪] 𝒪)
  (hx₀ : IsLocalHom (x₀ : D₀.R →+* 𝒪)) (hθ : IsLocalHom (θ : D'.R →+* D₀.R))
  (U U' : Matrix (Fin 2) (Fin 2) 𝒪) (m : ℕ) [NeZero m]
  (g₀ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)
  (φ : Φ' D₀ D' θ x₀ →ₗ[𝒪] Rm 𝒪 m)

local notation "G_ℚ" => AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ

theorem exists_basis_toMatrix_eq_Ftil (hUU' : U * U' = 1) :
    haveI := isLocalHom_xPrime D₀ D' θ x₀ hx₀ hθ
    ∃ bt : Module.Basis (Fin 2) (Am 𝒪 m) (D'.ρ.baseChangeAlong
        (xOfCotangentHom (xPrime D₀ D' θ x₀) φ : D'.R →+* Am 𝒪 m)
        (isLocalHom_xOfCotangentHom (xPrime D₀ D' θ x₀) φ)).V,
      ∀ g : G_ℚ,
        LinearMap.toMatrix bt bt ((D'.ρ.baseChangeAlong
          (xOfCotangentHom (xPrime D₀ D' θ x₀) φ : D'.R →+* Am 𝒪 m)
          (isLocalHom_xOfCotangentHom (xPrime D₀ D' θ x₀) φ)).ρ g) =
        Ftil D₀ D' θ x₀ U U' m g₀ φ g := by
  classical
  haveI hx' := isLocalHom_xPrime D₀ D' θ x₀ hx₀ hθ
  have hd := PRungL2.Obj.toMatrix_dualNumber_eq D₀ D' θ x₀ hx₀ hθ m φ
  letI : Algebra D'.R (Am 𝒪 m) :=
    (xOfCotangentHom (xPrime D₀ D' θ x₀) φ : D'.R →+* Am 𝒪 m).toAlgebra
  set ρt : GaloisRepAdic (Am 𝒪 m) := D'.ρ.baseChangeAlong
    (xOfCotangentHom (xPrime D₀ D' θ x₀) φ : D'.R →+* Am 𝒪 m)
    (isLocalHom_xOfCotangentHom (xPrime D₀ D' θ x₀) φ) with hρt
  let c : Module.Basis (Fin 2) (Am 𝒪 m) ρt.V := (bD D').baseChange (Am 𝒪 m)
  have hdict : ∀ g : G_ℚ, LinearMap.toMatrix c c (ρt.ρ g) = Mtil D₀ D' θ x₀ m φ g := hd
  clear hd
  set W : Matrix (Fin 2) (Fin 2) (Am 𝒪 m) := Wmat D₀ D' θ x₀ U U' m g₀ φ with hW
  set W' : Matrix (Fin 2) (Fin 2) (Am 𝒪 m) := Wmat' D₀ D' θ x₀ U U' m g₀ φ with hW'
  have hWW' : W * W' = 1 := Wmat_mul_Wmat' D₀ D' θ x₀ U U' m g₀ φ hUU'
  have hWdet : IsUnit W.det := Matrix.isUnit_det_of_right_inverse hWW'
  let Lq : ρt.V ≃ₗ[Am 𝒪 m] ρt.V := Matrix.toLinearEquiv c W hWdet
  refine ⟨c.map Lq, fun g => ?_⟩
  have h1 : c.toMatrix (c.map Lq) = W := by
    refine Matrix.ext fun i j => ?_
    rw [Module.Basis.toMatrix_apply, Module.Basis.map_apply, Matrix.toLinearEquiv_apply, Matrix.toLin_self,
      map_sum, Finsupp.finsetSum_apply]
    simp only [map_smul, Module.Basis.repr_self, Finsupp.smul_single, smul_eq_mul, mul_one,
      Finsupp.single_apply]
    rw [Finset.sum_eq_single i (fun k _ hk => if_neg hk) (fun h => absurd (Finset.mem_univ i) h), if_pos rfl]
  set bt := c.map Lq with hbt
  have hflip0 := Module.Basis.toMatrix_mul_toMatrix_flip bt c
  have h2 : bt.toMatrix c = W' := by
    calc bt.toMatrix c = bt.toMatrix c * (c.toMatrix bt * W') := by rw [h1, hWW', Matrix.mul_one]
      _ = (bt.toMatrix c * c.toMatrix bt) * W' := by rw [Matrix.mul_assoc]
      _ = W' := by rw [hflip0, Matrix.one_mul]
  have key := basis_toMatrix_mul_linearMap_toMatrix_mul_basis_toMatrix bt c bt c (ρt.ρ g)
  simp only [h1, h2] at key
  rw [← key, hdict g, Ftil_eq_conj]

theorem vector_facts_of_basis
    (P : ValuationSubring (AlgebraicClosure ℚ))
    (bt : haveI := isLocalHom_xPrime D₀ D' θ x₀ hx₀ hθ
      Module.Basis (Fin 2) (Am 𝒪 m) (D'.ρ.baseChangeAlong
        (xOfCotangentHom (xPrime D₀ D' θ x₀) φ : D'.R →+* Am 𝒪 m)
        (isLocalHom_xOfCotangentHom (xPrime D₀ D' θ x₀) φ)).V)
    (hbt : haveI := isLocalHom_xPrime D₀ D' θ x₀ hx₀ hθ
      ∀ g : G_ℚ,
        LinearMap.toMatrix bt bt ((D'.ρ.baseChangeAlong
          (xOfCotangentHom (xPrime D₀ D' θ x₀) φ : D'.R →+* Am 𝒪 m)
          (isLocalHom_xOfCotangentHom (xPrime D₀ D' θ x₀) φ)).ρ g) =
        Ftil D₀ D' θ x₀ U U' m g₀ φ g)
    (hF10 : ∀ g ∈ P.decompositionSubgroup ℚ, Ftil D₀ D' θ x₀ U U' m g₀ φ g 1 0 = 0)
    (hF11 : ∀ τ ∈ P.inertiaSubgroupIn ℚ, Ftil D₀ D' θ x₀ U U' m g₀ φ τ 1 1 = 1) :
    haveI := isLocalHom_xPrime D₀ D' θ x₀ hx₀ hθ
    (∀ σ ∈ P.decompositionSubgroup ℚ,
      (D'.ρ.baseChangeAlong (xOfCotangentHom (xPrime D₀ D' θ x₀) φ : D'.R →+* Am 𝒪 m)
        (isLocalHom_xOfCotangentHom (xPrime D₀ D' θ x₀) φ)).ρ σ (bt 0) ∈ (Am 𝒪 m) ∙ bt 0) ∧
    (∀ τ ∈ P.inertiaSubgroupIn ℚ, ∀ v,
      (D'.ρ.baseChangeAlong (xOfCotangentHom (xPrime D₀ D' θ x₀) φ : D'.R →+* Am 𝒪 m)
        (isLocalHom_xOfCotangentHom (xPrime D₀ D' θ x₀) φ)).ρ τ v - v ∈ (Am 𝒪 m) ∙ bt 0) ∧
    (∀ τ ∈ P.inertiaSubgroupIn ℚ,
      (D'.ρ.baseChangeAlong (xOfCotangentHom (xPrime D₀ D' θ x₀) φ : D'.R →+* Am 𝒪 m)
        (isLocalHom_xOfCotangentHom (xPrime D₀ D' θ x₀) φ)).ρ τ (bt 1) - bt 1 =
        (Ftil D₀ D' θ x₀ U U' m g₀ φ τ 0 1) • bt 0) := by
  haveI hx' := isLocalHom_xPrime D₀ D' θ x₀ hx₀ hθ
  have hID : P.inertiaSubgroupIn ℚ ≤ P.decompositionSubgroup ℚ := Subgroup.map_subtype_le _
  refine ⟨fun σ hσ => ?_, fun τ hτ v => ?_, fun τ hτ => ?_⟩
  · exact PRungBasisVec.apply_zero_mem_span bt _ _ (hbt σ) (hF10 σ hσ)
  · exact PRungBasisVec.sub_mem_span bt _ _ (hbt τ) (hF10 τ (hID hτ)) (hF11 τ hτ) v
  · exact PRungBasisVec.apply_one_sub_eq bt _ _ (hbt τ) (hF11 τ hτ)

end PRungL2.Obj
p2m_reactivate "P2MW.S_GaloisRep_DeformationRingData_exists_localInvariant_of_ordinaryLine.PRungD P2MW.S_GaloisRep_DeformationRingData_exists_localInvariant_of_ordinaryLine.PRungInvDict"
p2m_reactivate "P2MW.S_GaloisRep_DeformationRingData_exists_localInvariant_of_ordinaryLine.PRungD P2MW.S_GaloisRep_DeformationRingData_exists_localInvariant_of_ordinaryLine.PRungInvDict"

namespace PRungL2
namespace E4

theorem isUnit_natCast_of_coprime_of_mem {R : Type} [CommRing R] [IsLocalRing R] {p q : ℕ}
    (hcop : Nat.Coprime p q) (hp : (p : R) ∈ IsLocalRing.maximalIdeal R) : IsUnit (q : R) := by
  by_contra hq
  have hqm : (q : R) ∈ IsLocalRing.maximalIdeal R := (IsLocalRing.mem_maximalIdeal _).mpr hq
  obtain ⟨u, v, huv⟩ := (Nat.Coprime.cast (R := R) hcop)
  have h1 : (1 : R) ∈ IsLocalRing.maximalIdeal R := by
    rw [← huv]
    exact Ideal.add_mem _ (Ideal.mul_mem_left _ _ hp) (Ideal.mul_mem_left _ _ hqm)
  exact (IsLocalRing.maximalIdeal.isMaximal R).ne_top ((Ideal.eq_top_iff_one _).mpr h1)

theorem isUnit_add_of_mem {R : Type} [CommRing R] [IsLocalRing R] {u x : R} (hu : IsUnit u)
    (hx : x ∈ IsLocalRing.maximalIdeal R) : IsUnit (u + x) := by
  by_contra h
  have h' : u + x ∈ IsLocalRing.maximalIdeal R := (IsLocalRing.mem_maximalIdeal _).mpr h
  have : u ∈ IsLocalRing.maximalIdeal R := by
    have := Ideal.sub_mem _ h' hx
    rwa [add_sub_cancel_right] at this
  exact (IsLocalRing.mem_maximalIdeal _).mp this hu

theorem exists_unitGap_inertia {R : Type} [CommRing R] [IsLocalRing R]
    (p : ℕ) (hp : p.Prime) (hp2 : p ≠ 2) (hp𝔪 : (p : R) ∈ IsLocalRing.maximalIdeal R)
    (P : ValuationSubring (AlgebraicClosure ℚ)) (hP : P.LiesOverPrime p)
    (F : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) → Matrix (Fin 2) (Fin 2) R)
    (hI : ∀ τ ∈ P.inertiaSubgroupIn ℚ, F τ 1 0 = 0 ∧ F τ 1 1 = 1)
    (hdet : ∀ (g : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (n a : ℕ),
      (∀ μ : AlgebraicClosure ℚ, μ ^ p ^ n = 1 → g μ = μ ^ a) → (F g).det - (a : R) ∈ Ideal.span {((p ^ n : ℕ) : R)})
    (S : Type) [CommRing S] [Algebra R S] :
    ∃ g₀ ∈ P.inertiaSubgroupIn ℚ,
      IsUnit (((F g₀).map (algebraMap R S)) 0 0 - ((F g₀).map (algebraMap R S)) 1 1) := by
  haveI : Fact p.Prime := ⟨hp⟩
  obtain ⟨τ, hτI, hτ⟩ :=
    ValuationSubring.exists_mem_inertiaSubgroupIn_apply_eq_pow_of_pow_prime_pow_eq_one P hp hP 1 (-1)
  set a : ℕ := ((-1 : (ZMod (p ^ 1))ˣ) : ZMod (p ^ 1)).val with ha
  refine ⟨τ, hτI, ?_⟩

  have h1 : (F τ).det - (a : R) ∈ IsLocalRing.maximalIdeal R := by
    refine (Ideal.span_singleton_le_iff_mem _).mpr ?_ (hdet τ 1 a hτ)
    rw [pow_one]; exact hp𝔪
  have hdetF : (F τ).det = F τ 0 0 := by
    rw [Matrix.det_fin_two, (hI τ hτI).1, (hI τ hτI).2, mul_one, mul_zero, sub_zero]

  have hdvd : p ^ 1 ∣ a + 1 := by
    refine (CharP.cast_eq_zero_iff (ZMod (p ^ 1)) (p ^ 1) (a + 1)).mp ?_
    rw [Nat.cast_add, Nat.cast_one, ha, ZMod.natCast_zmod_val, Units.val_neg, Units.val_one, neg_add_cancel]
  have h2 : (a : R) + 1 ∈ IsLocalRing.maximalIdeal R := by
    obtain ⟨c, hc⟩ := hdvd
    have : ((a + 1 : ℕ) : R) = (p : R) * (c : R) := by rw [hc, pow_one, Nat.cast_mul]
    rw [← Nat.cast_add_one, this]
    exact Ideal.mul_mem_right _ _ hp𝔪

  have h2u : IsUnit (2 : R) := by
    have := isUnit_natCast_of_coprime_of_mem ((Nat.coprime_primes hp Nat.prime_two).mpr hp2) hp𝔪
    exact_mod_cast this
  have hunit : IsUnit (F τ 0 0 - F τ 1 1) := by
    rw [(hI τ hτI).2]
    have e : F τ 0 0 - 1 = -2 + (((F τ).det - (a : R)) + ((a : R) + 1)) := by rw [hdetF]; ring
    rw [e]
    exact isUnit_add_of_mem h2u.neg (Ideal.add_mem _ h1 h2)
  have := hunit.map (algebraMap R S)
  rwa [map_sub, ← Matrix.map_apply (f := algebraMap R S), ← Matrix.map_apply (f := algebraMap R S)] at this

end PRungL2.E4
p2m_reactivate "P2MW.S_GaloisRep_DeformationRingData_exists_localInvariant_of_ordinaryLine.PRungD P2MW.S_GaloisRep_DeformationRingData_exists_localInvariant_of_ordinaryLine.PRungInvDict"
p2m_reactivate "P2MW.S_GaloisRep_DeformationRingData_exists_localInvariant_of_ordinaryLine.PRungD P2MW.S_GaloisRep_DeformationRingData_exists_localInvariant_of_ordinaryLine.PRungInvDict"

namespace PRungL2
namespace E3Lin

open TrivSqZeroExt

variable {S : Type} [CommRing S] {V : Type} [AddCommGroup V] [Module (TrivSqZeroExt S S) V]
  (cA : Module.Basis (Fin 2) (TrivSqZeroExt S S) V) (f : V →ₗ[TrivSqZeroExt S S] V)
  (F Λ : Matrix (Fin 2) (Fin 2) S)
  (hf : LinearMap.toMatrix cA cA f = F.map TrivSqZeroExt.inl + Λ.map TrivSqZeroExt.inr)

include hf in
theorem repr_apply_basis (i j : Fin 2) : cA.repr (f (cA j)) i = inl (F i j) + inr (Λ i j) := by
  rw [← LinearMap.toMatrix_apply cA cA f i j, hf, Matrix.add_apply, Matrix.map_apply, Matrix.map_apply]

include hf in
theorem repr_apply (v : V) (i : Fin 2) : cA.repr (f v) i =
    (inl (F i 0) + inr (Λ i 0)) * cA.repr v 0 + (inl (F i 1) + inr (Λ i 1)) * cA.repr v 1 := by
  have hx : f v = cA.repr v 0 • f (cA 0) + cA.repr v 1 • f (cA 1) := by
    conv_lhs => rw [← cA.sum_repr v]
    rw [Fin.sum_univ_two, map_add, map_smul, map_smul]
  rw [hx, map_add, map_smul, map_smul, Finsupp.add_apply, Finsupp.smul_apply, Finsupp.smul_apply,
    smul_eq_mul, smul_eq_mul, repr_apply_basis cA f F Λ hf, repr_apply_basis cA f F Λ hf,
    mul_comm (cA.repr v 0), mul_comm (cA.repr v 1)]

theorem repr_smul (s : TrivSqZeroExt S S) (x : V) (i : Fin 2) : cA.repr (s • x) i = s * cA.repr x i := by
  rw [map_smul, Finsupp.smul_apply, smul_eq_mul]

include hf in

theorem fst_shape_of_sub_mem (v : V) (hF10 : F 1 0 = 0) (hu : IsUnit (F 0 0 - 1))
    (h : f (cA 0) - cA 0 ∈ (TrivSqZeroExt S S) ∙ v) :
    (cA.repr v 1).fst = 0 ∧ IsUnit (cA.repr v 0).fst := by
  obtain ⟨a₁, ha₁⟩ := Submodule.mem_span_singleton.mp h
  have e10 : a₁.fst * (cA.repr v 0).fst = F 0 0 - 1 := by
    have h := congrArg (fun x => (cA.repr x 0).fst) ha₁
    simp only [repr_smul, map_sub, Finsupp.coe_sub, Pi.sub_apply, repr_apply_basis cA f F Λ hf,
      Module.Basis.repr_self, Finsupp.single_eq_same, fst_mul, fst_sub, fst_add, fst_inl, fst_inr,
      fst_one, add_zero] at h
    exact h
  have e11 : a₁.fst * (cA.repr v 1).fst = 0 := by
    have h := congrArg (fun x => (cA.repr x 1).fst) ha₁
    simp only [repr_smul, map_sub, Finsupp.coe_sub, Pi.sub_apply, repr_apply_basis cA f F Λ hf,
      Module.Basis.repr_self, Finsupp.single_eq_of_ne (show (1 : Fin 2) ≠ 0 from one_ne_zero), fst_mul,
      fst_add, fst_inl, fst_inr, add_zero, sub_zero, hF10] at h
    exact h
  have hprod : IsUnit (a₁.fst * (cA.repr v 0).fst) := e10 ▸ hu
  exact ⟨((isUnit_of_mul_isUnit_left hprod).mul_right_eq_zero).mp e11, isUnit_of_mul_isUnit_right hprod⟩

include hf in

theorem lowerLeft_rel_of_mem (v : V) (hF10 : F 1 0 = 0) (hb0 : (cA.repr v 1).fst = 0)
    (hau : IsUnit (cA.repr v 0).fst) (h : f v ∈ (TrivSqZeroExt S S) ∙ v) :
    Λ 1 0 * (cA.repr v 0).fst + (F 1 1 - F 0 0) * (cA.repr v 1).snd = 0 := by
  obtain ⟨μ, hμ⟩ := Submodule.mem_span_singleton.mp h
  have h0 : μ.fst * (cA.repr v 0).fst = F 0 0 * (cA.repr v 0).fst := by
    have h := congrArg (fun x => (cA.repr x 0).fst) hμ
    simp only [repr_smul, repr_apply cA f F Λ hf, fst_mul, fst_add, fst_inl, fst_inr, add_zero, hb0,
      mul_zero] at h
    exact h
  have hμ0 : μ.fst = F 0 0 := hau.mul_left_injective h0
  have h1 : μ.fst * (cA.repr v 1).snd = (cA.repr v 0).fst * Λ 1 0 + F 1 1 * (cA.repr v 1).snd := by
    have h := congrArg (fun x => (cA.repr x 1).snd) hμ
    simp only [repr_smul, repr_apply cA f F Λ hf, snd_mul, snd_add, fst_add, fst_inl, snd_inl,
      fst_inr, snd_inr, op_smul_eq_smul, smul_eq_mul, hb0, hF10, zero_add, add_zero, zero_mul] at h
    linear_combination h
  rw [hμ0] at h1
  linear_combination -h1

include hf in

theorem diag_rel_of_sub_mem (v : V) (hb0 : (cA.repr v 1).fst = 0)
    (h : f (cA 1) - cA 1 ∈ (TrivSqZeroExt S S) ∙ v) :
    Λ 1 1 * (cA.repr v 0).fst = F 0 1 * (cA.repr v 1).snd := by
  obtain ⟨a', ha'⟩ := Submodule.mem_span_singleton.mp h
  have f0 : a'.fst * (cA.repr v 0).fst = F 0 1 := by
    have h := congrArg (fun x => (cA.repr x 0).fst) ha'
    simp only [repr_smul, map_sub, Finsupp.coe_sub, Pi.sub_apply, repr_apply_basis cA f F Λ hf,
      Module.Basis.repr_self, Finsupp.single_eq_of_ne (show (0 : Fin 2) ≠ 1 from zero_ne_one), fst_mul,
      fst_add, fst_inl, fst_inr, add_zero, sub_zero] at h
    exact h
  have f1 : a'.fst * (cA.repr v 1).snd = Λ 1 1 := by
    have h := congrArg (fun x => (cA.repr x 1).snd) ha'
    simp only [repr_smul, map_sub, Finsupp.coe_sub, Pi.sub_apply, repr_apply_basis cA f F Λ hf,
      Module.Basis.repr_self, Finsupp.single_eq_same, snd_mul, snd_sub, snd_add, snd_inl, snd_inr,
      snd_one, op_smul_eq_smul, smul_eq_mul, hb0, zero_add, add_zero, zero_mul, sub_zero] at h
    exact h
  rw [← f1, ← f0]
  ring

theorem mul_inverse_mul_cancel (a b : S) (ha : IsUnit a) : b * Ring.inverse a * a = b := by
  rw [mul_assoc, Ring.inverse_mul_cancel _ ha, mul_one]

theorem pin_w {l w f00 f11 : S} (h : l + w * (f11 - f00) = 0) (hu : IsUnit (f00 - f11)) :
    l * Ring.inverse (f00 - f11) = w := by
  have hd : w * (f00 - f11) = l := by linear_combination -h
  rw [← hd, mul_assoc, Ring.mul_inverse_cancel _ hu, mul_one]

include hf in

theorem lowerLeft_eq_zero (v : V) (hF10 : F 1 0 = 0) (hb0 : (cA.repr v 1).fst = 0)
    (hau : IsUnit (cA.repr v 0).fst) (h : f v ∈ (TrivSqZeroExt S S) ∙ v) (w : S)
    (hwa : w * (cA.repr v 0).fst = (cA.repr v 1).snd) : Λ 1 0 + w * (F 1 1 - F 0 0) = 0 := by
  have hB := lowerLeft_rel_of_mem cA f F Λ hf v hF10 hb0 hau h
  have h2 : (Λ 1 0 + w * (F 1 1 - F 0 0)) * (cA.repr v 0).fst = 0 := by
    linear_combination hB + (F 1 1 - F 0 0) * hwa
  exact (hau.mul_left_eq_zero).mp h2

include hf in

theorem diag_eq_zero (v : V) (hb0 : (cA.repr v 1).fst = 0) (hau : IsUnit (cA.repr v 0).fst)
    (h : f (cA 1) - cA 1 ∈ (TrivSqZeroExt S S) ∙ v) (w : S)
    (hwa : w * (cA.repr v 0).fst = (cA.repr v 1).snd) : Λ 1 1 - w * F 0 1 = 0 := by
  have hC := diag_rel_of_sub_mem cA f F Λ hf v hb0 h
  have h3 : (Λ 1 1 - w * F 0 1) * (cA.repr v 0).fst = 0 := by
    linear_combination hC - F 0 1 * hwa
  exact (hau.mul_left_eq_zero).mp h3

end PRungL2.E3Lin
p2m_reactivate "P2MW.S_GaloisRep_DeformationRingData_exists_localInvariant_of_ordinaryLine.PRungD P2MW.S_GaloisRep_DeformationRingData_exists_localInvariant_of_ordinaryLine.PRungInvDict"
p2m_reactivate "P2MW.S_GaloisRep_DeformationRingData_exists_localInvariant_of_ordinaryLine.PRungD P2MW.S_GaloisRep_DeformationRingData_exists_localInvariant_of_ordinaryLine.PRungInvDict"

namespace PRungL2
namespace Holes

open PRungD GaloisRep PRungL2.Setup PRungL2.Obj

variable {𝒪 : Type} [CommRing 𝒪] [IsDomain 𝒪] [IsDiscreteValuationRing 𝒪]
  [IsAdicComplete (IsLocalRing.maximalIdeal 𝒪) 𝒪]
  {ρbar : ResidualGaloisRep (IsLocalRing.ResidueField 𝒪)}
  {𝒟₀ 𝒟' : ∀ ⦃A : Type⦄ [CommRing A] [IsLocalRing A] [Algebra 𝒪 A], GaloisRepAdic A → Prop}
  (D₀ : DeformationRingData 𝒪 ρbar 𝒟₀) (D' : DeformationRingData 𝒪 ρbar 𝒟')
  (θ : D'.R →ₐ[𝒪] D₀.R) (x₀ : D₀.R →ₐ[𝒪] 𝒪)
  (hx₀ : IsLocalHom (x₀ : D₀.R →+* 𝒪)) (hθ : IsLocalHom (θ : D'.R →+* D₀.R))
  (p : ℕ) (hp : p.Prime) (hp2 : p ≠ 2)
  (P : ValuationSubring (AlgebraicClosure ℚ)) (hP : P.LiesOverPrime p)
  (U U' : Matrix (Fin 2) (Fin 2) 𝒪) (hU'U : U' * U = 1) (hUU' : U * U' = 1)
  (hD : ∀ g ∈ P.decompositionSubgroup ℚ, Fad D₀ D' θ x₀ U U' g 1 0 = 0)
  (hI : ∀ τ ∈ P.inertiaSubgroupIn ℚ, Fad D₀ D' θ x₀ U U' τ 1 0 = 0 ∧ Fad D₀ D' θ x₀ U U' τ 1 1 = 1)
  (hdet : ∀ g : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ, ∀ (n a : ℕ),
      (∀ μ : AlgebraicClosure ℚ, μ ^ p ^ n = 1 → g μ = μ ^ a) →
        (Fad D₀ D' θ x₀ U U' g).det - (a : 𝒪) ∈ Ideal.span {((p ^ n : ℕ) : 𝒪)})
  (hp𝔪 : (p : 𝒪) ∈ IsLocalRing.maximalIdeal 𝒪)
  (m : ℕ) [NeZero m]
  (g₀ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (hg₀ : g₀ ∈ P.inertiaSubgroupIn ℚ)
  (hg₀u : IsUnit (Fadm D₀ D' θ x₀ U U' m g₀ 0 0 - Fadm D₀ D' θ x₀ U U' m g₀ 1 1))
  (φ : Φ' D₀ D' θ x₀ →ₗ[𝒪] Rm 𝒪 m)

include hP hD hI hg₀ hg₀u in

theorem e3_keyFacts
    (cA : haveI := isLocalHom_xPrime D₀ D' θ x₀ hx₀ hθ
      Module.Basis (Fin 2) (Am 𝒪 m) (D'.ρ.baseChangeAlong
        (xOfCotangentHom (xPrime D₀ D' θ x₀) φ : D'.R →+* Am 𝒪 m)
        (isLocalHom_xOfCotangentHom (xPrime D₀ D' θ x₀) φ)).V)
    (hcA : haveI := isLocalHom_xPrime D₀ D' θ x₀ hx₀ hθ
      ∀ g : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ,
        LinearMap.toMatrix cA cA ((D'.ρ.baseChangeAlong
          (xOfCotangentHom (xPrime D₀ D' θ x₀) φ : D'.R →+* Am 𝒪 m)
          (isLocalHom_xOfCotangentHom (xPrime D₀ D' θ x₀) φ)).ρ g) =
        (Fadm D₀ D' θ x₀ U U' m g).map TrivSqZeroExt.inl + (Lam D₀ D' θ x₀ U U' m φ g).map TrivSqZeroExt.inr)
    (hord : haveI := isLocalHom_xPrime D₀ D' θ x₀ hx₀ hθ
      (D'.ρ.baseChangeAlong (xOfCotangentHom (xPrime D₀ D' θ x₀) φ : D'.R →+* Am 𝒪 m)
        (isLocalHom_xOfCotangentHom (xPrime D₀ D' θ x₀) φ)).IsOrdinaryAt p) :
    (∀ g ∈ P.decompositionSubgroup ℚ,
      Lam D₀ D' θ x₀ U U' m φ g 1 0 +
        w₁ D₀ D' θ x₀ U U' m g₀ φ * (Fadm D₀ D' θ x₀ U U' m g 1 1 - Fadm D₀ D' θ x₀ U U' m g 0 0) = 0) ∧
    (∀ τ ∈ P.inertiaSubgroupIn ℚ,
      Lam D₀ D' θ x₀ U U' m φ τ 1 1 - w₁ D₀ D' θ x₀ U U' m g₀ φ * Fadm D₀ D' θ x₀ U U' m τ 0 1 = 0) := by
  classical
  haveI hxP := isLocalHom_xPrime D₀ D' θ x₀ hx₀ hθ
  have hID : P.inertiaSubgroupIn ℚ ≤ P.decompositionSubgroup ℚ := Subgroup.map_subtype_le _
  set F : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) → Matrix (Fin 2) (Fin 2) (Rm 𝒪 m) :=
    Fadm D₀ D' θ x₀ U U' m with hFdef
  set Λ : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) → Matrix (Fin 2) (Fin 2) (Rm 𝒪 m) :=
    Lam D₀ D' θ x₀ U U' m φ with hΛdef

  have hF10 : ∀ g ∈ P.decompositionSubgroup ℚ, F g 1 0 = 0 := fun g hg => by
    simp only [hFdef, Fadm, Matrix.map_apply, hD g hg, map_zero]
  have hF11 : F g₀ 1 1 = 1 := by
    simp only [hFdef, Fadm, Matrix.map_apply, (hI g₀ hg₀).2, map_one]
  have hu : IsUnit (F g₀ 0 0 - 1) := by rw [← hF11]; exact hg₀u

  obtain ⟨Lt, ⟨c, rfl⟩, hLD, hLI⟩ := hord P hP
  obtain ⟨hb0, hau⟩ := PRungL2.E3Lin.fst_shape_of_sub_mem cA _ (F g₀) (Λ g₀) (hcA g₀) (c 0)
    (hF10 g₀ (hID hg₀)) hu (hLI g₀ hg₀ (cA 0))
  have hwa := PRungL2.E3Lin.mul_inverse_mul_cancel (cA.repr (c 0) 0).fst (cA.repr (c 0) 1).snd hau

  have key : ∀ g ∈ P.decompositionSubgroup ℚ,
      Λ g 1 0 + ((cA.repr (c 0) 1).snd * Ring.inverse (cA.repr (c 0) 0).fst) * (F g 1 1 - F g 0 0) = 0 :=
    fun g hg => PRungL2.E3Lin.lowerLeft_eq_zero cA _ (F g) (Λ g) (hcA g) (c 0) (hF10 g hg) hb0 hau
      (hLD g hg (c 0) (Submodule.mem_span_singleton_self (c 0))) _ hwa

  have hw₁ : w₁ D₀ D' θ x₀ U U' m g₀ φ = ((cA.repr (c 0) 1).snd * Ring.inverse (cA.repr (c 0) 0).fst) := by
    show Λ g₀ 1 0 * Ring.inverse (F g₀ 0 0 - F g₀ 1 1) = _
    exact PRungL2.E3Lin.pin_w (key g₀ (hID hg₀)) hg₀u
  refine ⟨fun g hg => ?_, fun τ hτ => ?_⟩
  · rw [hw₁]; exact key g hg
  · rw [hw₁]
    exact PRungL2.E3Lin.diag_eq_zero cA _ (F τ) (Λ τ) (hcA τ) (c 0) hb0 hau (hLI τ hτ (cA 1)) _ hwa

include hP hD hI hg₀ hg₀u in

theorem lowerLeft_eps_eq_zero
    (cA : haveI := isLocalHom_xPrime D₀ D' θ x₀ hx₀ hθ
      Module.Basis (Fin 2) (Am 𝒪 m) (D'.ρ.baseChangeAlong
        (xOfCotangentHom (xPrime D₀ D' θ x₀) φ : D'.R →+* Am 𝒪 m)
        (isLocalHom_xOfCotangentHom (xPrime D₀ D' θ x₀) φ)).V)
    (hcA : haveI := isLocalHom_xPrime D₀ D' θ x₀ hx₀ hθ
      ∀ g : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ,
        LinearMap.toMatrix cA cA ((D'.ρ.baseChangeAlong
          (xOfCotangentHom (xPrime D₀ D' θ x₀) φ : D'.R →+* Am 𝒪 m)
          (isLocalHom_xOfCotangentHom (xPrime D₀ D' θ x₀) φ)).ρ g) =
        (Fadm D₀ D' θ x₀ U U' m g).map TrivSqZeroExt.inl + (Lam D₀ D' θ x₀ U U' m φ g).map TrivSqZeroExt.inr)
    (hord : haveI := isLocalHom_xPrime D₀ D' θ x₀ hx₀ hθ
      (D'.ρ.baseChangeAlong (xOfCotangentHom (xPrime D₀ D' θ x₀) φ : D'.R →+* Am 𝒪 m)
        (isLocalHom_xOfCotangentHom (xPrime D₀ D' θ x₀) φ)).IsOrdinaryAt p) :
    ∀ g ∈ P.decompositionSubgroup ℚ,
      Lam D₀ D' θ x₀ U U' m φ g 1 0 +
        w₁ D₀ D' θ x₀ U U' m g₀ φ * (Fadm D₀ D' θ x₀ U U' m g 1 1 - Fadm D₀ D' θ x₀ U U' m g 0 0) = 0 := by
  exact (e3_keyFacts D₀ D' θ x₀ hx₀ hθ p P hP U U' hD hI m g₀ hg₀ hg₀u φ cA hcA hord).1

include hP hD hI hg₀ hg₀u in

theorem diag_eps_eq_zero_on_inertia
    (cA : haveI := isLocalHom_xPrime D₀ D' θ x₀ hx₀ hθ
      Module.Basis (Fin 2) (Am 𝒪 m) (D'.ρ.baseChangeAlong
        (xOfCotangentHom (xPrime D₀ D' θ x₀) φ : D'.R →+* Am 𝒪 m)
        (isLocalHom_xOfCotangentHom (xPrime D₀ D' θ x₀) φ)).V)
    (hcA : haveI := isLocalHom_xPrime D₀ D' θ x₀ hx₀ hθ
      ∀ g : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ,
        LinearMap.toMatrix cA cA ((D'.ρ.baseChangeAlong
          (xOfCotangentHom (xPrime D₀ D' θ x₀) φ : D'.R →+* Am 𝒪 m)
          (isLocalHom_xOfCotangentHom (xPrime D₀ D' θ x₀) φ)).ρ g) =
        (Fadm D₀ D' θ x₀ U U' m g).map TrivSqZeroExt.inl + (Lam D₀ D' θ x₀ U U' m φ g).map TrivSqZeroExt.inr)
    (hord : haveI := isLocalHom_xPrime D₀ D' θ x₀ hx₀ hθ
      (D'.ρ.baseChangeAlong (xOfCotangentHom (xPrime D₀ D' θ x₀) φ : D'.R →+* Am 𝒪 m)
        (isLocalHom_xOfCotangentHom (xPrime D₀ D' θ x₀) φ)).IsOrdinaryAt p) :
    ∀ τ ∈ P.inertiaSubgroupIn ℚ,
      Lam D₀ D' θ x₀ U U' m φ τ 1 1 - w₁ D₀ D' θ x₀ U U' m g₀ φ * Fadm D₀ D' θ x₀ U U' m τ 0 1 = 0 := by
  exact (e3_keyFacts D₀ D' θ x₀ hx₀ hθ p P hP U U' hD hI m g₀ hg₀ hg₀u φ cA hcA hord).2

omit hU'U hUU' hD hI hdet hp𝔪 hg₀ hg₀u in

theorem exists_basis_matrix_eq (hUU' : U * U' = 1) :
    haveI := isLocalHom_xPrime D₀ D' θ x₀ hx₀ hθ
    ∃ cA : Module.Basis (Fin 2) (Am 𝒪 m) (D'.ρ.baseChangeAlong
        (xOfCotangentHom (xPrime D₀ D' θ x₀) φ : D'.R →+* Am 𝒪 m)
        (isLocalHom_xOfCotangentHom (xPrime D₀ D' θ x₀) φ)).V,
      ∀ g : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ,
        LinearMap.toMatrix cA cA ((D'.ρ.baseChangeAlong
          (xOfCotangentHom (xPrime D₀ D' θ x₀) φ : D'.R →+* Am 𝒪 m)
          (isLocalHom_xOfCotangentHom (xPrime D₀ D' θ x₀) φ)).ρ g) =
        (Fadm D₀ D' θ x₀ U U' m g).map TrivSqZeroExt.inl + (Lam D₀ D' θ x₀ U U' m φ g).map TrivSqZeroExt.inr := by
  classical
  haveI hx' := isLocalHom_xPrime D₀ D' θ x₀ hx₀ hθ
  have hd := PRungL2.Obj.toMatrix_dualNumber_eq D₀ D' θ x₀ hx₀ hθ m φ
  letI : Algebra D'.R (Am 𝒪 m) :=
    (xOfCotangentHom (xPrime D₀ D' θ x₀) φ : D'.R →+* Am 𝒪 m).toAlgebra
  set ρt : GaloisRepAdic (Am 𝒪 m) := D'.ρ.baseChangeAlong
    (xOfCotangentHom (xPrime D₀ D' θ x₀) φ : D'.R →+* Am 𝒪 m)
    (isLocalHom_xOfCotangentHom (xPrime D₀ D' θ x₀) φ) with hρt
  let c : Module.Basis (Fin 2) (Am 𝒪 m) ρt.V := (bD D').baseChange (Am 𝒪 m)
  have hdict : ∀ g : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ, LinearMap.toMatrix c c (ρt.ρ g) =
      ((Mof D₀ D' θ x₀ g).map (algebraMap 𝒪 (Rm 𝒪 m))).map TrivSqZeroExt.inl +
        (Λₗspec D₀ D' θ x₀ m φ g).map TrivSqZeroExt.inr := hd
  clear hd

  let ι : 𝒪 →+* Am 𝒪 m := algebraMap 𝒪 (Am 𝒪 m)
  have hι : (⇑ι : 𝒪 → Am 𝒪 m) = (TrivSqZeroExt.inl : Rm 𝒪 m → Am 𝒪 m) ∘ ⇑(algebraMap 𝒪 (Rm 𝒪 m)) :=
    funext fun r => TrivSqZeroExt.algebraMap_eq_inl' _ _ _ r
  set UA : Matrix (Fin 2) (Fin 2) (Am 𝒪 m) := U.map ι with hUA
  set UA' : Matrix (Fin 2) (Fin 2) (Am 𝒪 m) := U'.map ι with hUA'
  have hUAUA' : UA * UA' = 1 := by
    rw [hUA, hUA', ← Matrix.map_mul, hUU', Matrix.map_one _ (map_zero _) (map_one _)]
  have hUAdet : IsUnit UA.det := Matrix.isUnit_det_of_right_inverse hUAUA'
  let Lq : ρt.V ≃ₗ[Am 𝒪 m] ρt.V := Matrix.toLinearEquiv c UA hUAdet
  refine ⟨c.map Lq, fun g => ?_⟩
  have h1 : c.toMatrix (c.map Lq) = UA := by
    refine Matrix.ext fun i j => ?_
    rw [Module.Basis.toMatrix_apply, Module.Basis.map_apply, Matrix.toLinearEquiv_apply, Matrix.toLin_self,
      map_sum, Finsupp.finset_sum_apply]
    simp only [map_smul, Module.Basis.repr_self, Finsupp.smul_single, smul_eq_mul, mul_one,
      Finsupp.single_apply]
    rw [Finset.sum_eq_single i (fun k _ hk => if_neg hk) (fun h => absurd (Finset.mem_univ i) h), if_pos rfl]
  set cA := c.map Lq with hcA
  have hflip0 := Module.Basis.toMatrix_mul_toMatrix_flip cA c
  have h2 : cA.toMatrix c = UA' := by
    calc cA.toMatrix c = cA.toMatrix c * (c.toMatrix cA * UA') := by rw [h1, hUAUA', Matrix.mul_one]
      _ = (cA.toMatrix c * c.toMatrix cA) * UA' := by rw [Matrix.mul_assoc]
      _ = UA' := by rw [hflip0, Matrix.one_mul]
  have key := basis_toMatrix_mul_linearMap_toMatrix_mul_basis_toMatrix cA c cA c (ρt.ρ g)

  simp only [h1, h2] at key
  rw [hdict g] at key
  rw [← key, hUA, hUA', hι, ← Matrix.map_map, ← Matrix.map_map, PRungTsze.conj_pair_eq]
  simp only [Fadm, Fad, Lam, PRungConjFam.conjFam_apply, Matrix.map_mul]

end PRungL2.Holes
p2m_reactivate "P2MW.S_GaloisRep_DeformationRingData_exists_localInvariant_of_ordinaryLine.PRungD P2MW.S_GaloisRep_DeformationRingData_exists_localInvariant_of_ordinaryLine.PRungInvDict"
p2m_reactivate "P2MW.S_GaloisRep_DeformationRingData_exists_localInvariant_of_ordinaryLine.PRungD P2MW.S_GaloisRep_DeformationRingData_exists_localInvariant_of_ordinaryLine.PRungInvDict"

namespace PRungL2
namespace Reindex

theorem corner_eq_kϖ_smul_add {K : Type} [Field K] {M : Type} [AddCommMonoid M]
    {F : Type} [FunLike F K K] [MonoidHomClass F K K] (τ : F) (ζ ϖ : K) (hϖ0 : ϖ ≠ 0)
    {t : ℕ} (n : Fin t → ℕ) (β : Fin t → K) (a : Fin t → M) (cτ : M)
    (hdec : ∀ k : Fin t → ℕ, (∀ i, τ (β i) = ζ ^ (k i) * β i) → cτ = ∑ i, (k i) • a i)
    (kϖ : ℕ) (hkϖ : τ ϖ = ζ ^ kϖ * ϖ) (k' : Fin t → ℕ)
    (hk' : ∀ i, τ (β i * (ϖ ^ n i)⁻¹) = ζ ^ (k' i) * (β i * (ϖ ^ n i)⁻¹)) :
    cτ = kϖ • ∑ i, (n i) • a i + ∑ i, (k' i) • a i := by
  have hβ : ∀ i, τ (β i) = ζ ^ (kϖ * n i + k' i) * β i := by
    intro i
    have hpow : ϖ ^ n i ≠ 0 := pow_ne_zero _ hϖ0
    have e1 : β i = (β i * (ϖ ^ n i)⁻¹) * ϖ ^ n i := by rw [inv_mul_cancel_right₀ hpow]
    conv_lhs => rw [e1, map_mul, map_pow, hk' i, hkϖ]
    rw [mul_pow, ← pow_mul,
      show ζ ^ k' i * (β i * (ϖ ^ n i)⁻¹) * (ζ ^ (kϖ * n i) * ϖ ^ n i) =
        ζ ^ (kϖ * n i + k' i) * (β i * (ϖ ^ n i)⁻¹ * ϖ ^ n i) by rw [pow_add]; ring,
      inv_mul_cancel_right₀ hpow]
  rw [hdec _ hβ, Finset.smul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [add_nsmul, mul_nsmul']

end PRungL2.Reindex
p2m_reactivate "P2MW.S_GaloisRep_DeformationRingData_exists_localInvariant_of_ordinaryLine.PRungD P2MW.S_GaloisRep_DeformationRingData_exists_localInvariant_of_ordinaryLine.PRungInvDict"
p2m_reactivate "P2MW.S_GaloisRep_DeformationRingData_exists_localInvariant_of_ordinaryLine.PRungD P2MW.S_GaloisRep_DeformationRingData_exists_localInvariant_of_ordinaryLine.PRungInvDict"

section PRungUmbrellaHelpers
open TrivSqZeroExt

theorem PRungTsze.snd_mul_eq_zero_of {R : Type} [CommRing R] (χ X : TrivSqZeroExt R R)
    (h : (χ ^ 2 - 1) * X = 0) (hr : X.fst = 0) : (χ.fst ^ 2 - 1) * X.snd = 0 := by
  have h2 := congrArg TrivSqZeroExt.snd h
  rw [snd_mul, snd_zero, hr, MulOpposite.op_zero, zero_smul, add_zero, fst_sub, fst_pow, fst_one,
    smul_eq_mul] at h2
  exact h2

end PRungUmbrellaHelpers
p2m_reactivate "P2MW.S_GaloisRep_DeformationRingData_exists_localInvariant_of_ordinaryLine.PRungD P2MW.S_GaloisRep_DeformationRingData_exists_localInvariant_of_ordinaryLine.PRungInvDict"

namespace PRungL2
namespace Obj

open PRungD GaloisRep PRungL2.Setup

variable {𝒪 : Type} [CommRing 𝒪] [IsDomain 𝒪] [IsDiscreteValuationRing 𝒪]
  [IsAdicComplete (IsLocalRing.maximalIdeal 𝒪) 𝒪]
  {ρbar : ResidualGaloisRep (IsLocalRing.ResidueField 𝒪)}
  {𝒟₀ 𝒟' : ∀ ⦃A : Type⦄ [CommRing A] [IsLocalRing A] [Algebra 𝒪 A], GaloisRepAdic A → Prop}
  (D₀ : DeformationRingData 𝒪 ρbar 𝒟₀) (D' : DeformationRingData 𝒪 ρbar 𝒟')
  (θ : D'.R →ₐ[𝒪] D₀.R) (x₀ : D₀.R →ₐ[𝒪] 𝒪)
  (hx₀ : IsLocalHom (x₀ : D₀.R →+* 𝒪)) (hθ : IsLocalHom (θ : D'.R →+* D₀.R))
  (U U' : Matrix (Fin 2) (Fin 2) 𝒪)

include hx₀ hθ in

theorem det_Ftil_sub_mem_span (m : ℕ) [NeZero m] (g₀ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)
    (φ : Φ' D₀ D' θ x₀ →ₗ[𝒪] Rm 𝒪 m) (hUU' : U * U' = 1) {p : ℕ}
    (hdet : haveI := isLocalHom_xPrime D₀ D' θ x₀ hx₀ hθ
      (D'.ρ.baseChangeAlong (xOfCotangentHom (xPrime D₀ D' θ x₀) φ : D'.R →+* Am 𝒪 m)
        (isLocalHom_xOfCotangentHom (xPrime D₀ D' θ x₀) φ)).DetIsCyclotomic p)
    (g : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (n a : ℕ)
    (hμ : ∀ μ : AlgebraicClosure ℚ, μ ^ p ^ n = 1 → g μ = μ ^ a) :
    (Ftil D₀ D' θ x₀ U U' m g₀ φ g).det - (a : Am 𝒪 m) ∈ Ideal.span {((p ^ n : ℕ) : Am 𝒪 m)} := by
  rw [det_Ftil_eq_det_Mtil D₀ D' θ x₀ U U' m g₀ φ hUU' g, det_Mtil_eq D₀ D' θ x₀ hx₀ hθ m φ g]
  exact hdet.2 n g a hμ

theorem det_Fadm_eq_natCast {p : ℕ} [NeZero p]
    (hdet : ∀ (g : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (n a : ℕ),
      (∀ μ : AlgebraicClosure ℚ, μ ^ p ^ n = 1 → g μ = μ ^ a) →
        (Fad D₀ D' θ x₀ U U' g).det - (a : 𝒪) ∈ Ideal.span {((p ^ n : ℕ) : 𝒪)})
    (L : ℕ) {N : ℕ} (hpN : ((p : ℕ) : Rm 𝒪 L) ^ N = 0) (ζ : AlgebraicClosure ℚ) (hζ : IsPrimitiveRoot ζ (p ^ N))
    (g : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (e : ℕ) (hg : g ζ = ζ ^ e) :
    (Fadm D₀ D' θ x₀ U U' L g).det = (e : Rm 𝒪 L) := by
  have h3 := hdet g N e (forall_pow_eq_one_apply_eq_pow ζ hζ g e hg)
  obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.mp h3
  have h4 : algebraMap 𝒪 (Rm 𝒪 L) ((Fad D₀ D' θ x₀ U U' g).det - (e : 𝒪)) = 0 := by
    rw [← hc, map_mul, map_natCast, Nat.cast_pow, hpN, mul_zero]
  rw [map_sub, map_natCast, sub_eq_zero, RingHom.map_det] at h4
  exact h4

end PRungL2.Obj
p2m_reactivate "P2MW.S_GaloisRep_DeformationRingData_exists_localInvariant_of_ordinaryLine.PRungD P2MW.S_GaloisRep_DeformationRingData_exists_localInvariant_of_ordinaryLine.PRungInvDict"
p2m_reactivate "P2MW.S_GaloisRep_DeformationRingData_exists_localInvariant_of_ordinaryLine.PRungD P2MW.S_GaloisRep_DeformationRingData_exists_localInvariant_of_ordinaryLine.PRungInvDict"

section PRungL2ChildStubs

end PRungL2ChildStubs
p2m_reactivate "P2MW.S_GaloisRep_DeformationRingData_exists_localInvariant_of_ordinaryLine.PRungD P2MW.S_GaloisRep_DeformationRingData_exists_localInvariant_of_ordinaryLine.PRungInvDict"

namespace PRungL2
namespace E3Level

open TrivSqZeroExt

theorem tsze_comap_fst_pow_eq_zero {R : Type} [CommRing R] (I : Ideal R) (k : ℕ) (hI : I ^ k = ⊥) :
    ∀ z ∈ (I.comap (TrivSqZeroExt.fstHom R R R)) ^ (k + 1), z = 0 := by
  set N : Ideal (TrivSqZeroExt R R) := I.comap (TrivSqZeroExt.fstHom R R R) with hN
  have hmemN : ∀ z : TrivSqZeroExt R R, z ∈ N ↔ z.fst ∈ I := fun z => Ideal.mem_comap

  have key : ∀ (j : ℕ) (z : TrivSqZeroExt R R), z ∈ N ^ j → z.fst ∈ I ^ j ∧ z.snd ∈ I ^ (j - 1) := by
    intro j
    induction j with
    | zero => intro z _; simp
    | succ j ih =>
      intro z hz
      have hz' : z ∈ N ^ j * N := (pow_succ N j) ▸ hz
      refine Submodule.mul_induction_on hz' (fun y hy n hn => ?_) (fun x y hx hy => ?_)
      · obtain ⟨hy1, hy2⟩ := ih y hy
        have hn1 : n.fst ∈ I := (hmemN n).mp hn
        refine ⟨?_, ?_⟩
        · simpa only [fst_mul, pow_succ] using Ideal.mul_mem_mul hy1 hn1
        · have h := Ideal.mul_mem_mul hn1 hy2
          rw [← pow_succ'] at h
          have h' : n.fst * y.snd ∈ I ^ j := Ideal.pow_le_pow_right (by omega) h
          simp only [snd_mul, op_smul_eq_smul, smul_eq_mul, Nat.add_sub_cancel]
          exact Ideal.add_mem _ (Ideal.mul_mem_right _ _ hy1) h'
      · exact ⟨by rw [fst_add]; exact Ideal.add_mem _ hx.1 hy.1,
          by rw [snd_add]; exact Ideal.add_mem _ hx.2 hy.2⟩
  intro z hz
  obtain ⟨h1, h2⟩ := key (k + 1) z hz
  rw [Nat.add_sub_cancel, hI] at h2
  have h1' : z.fst ∈ I ^ k := Ideal.pow_le_pow_right (Nat.le_succ k) h1
  rw [hI] at h1'
  exact TrivSqZeroExt.ext ((Submodule.mem_bot R).mp h1') ((Submodule.mem_bot R).mp h2)

variable (𝒪 : Type) [CommRing 𝒪] [IsDomain 𝒪] [IsDiscreteValuationRing 𝒪] (m : ℕ) [NeZero m]

theorem maximalIdeal_Rm_pow_eq_bot : IsLocalRing.maximalIdeal (PRungD.Rm 𝒪 m) ^ m = ⊥ := by
  rw [← IsLocalRing.map_maximalIdeal_of_surjective (Ideal.Quotient.mk ((IsLocalRing.maximalIdeal 𝒪) ^ m))
    Ideal.Quotient.mk_surjective, ← Ideal.map_pow, Ideal.map_quotient_self]

theorem eq_zero_of_mem_maximalIdeal_Am_pow :
    ∀ z ∈ IsLocalRing.maximalIdeal (PRungD.Am 𝒪 m) ^ (m + 1), z = 0 := by
  intro z hz
  have hle : IsLocalRing.maximalIdeal (PRungD.Am 𝒪 m) ≤
      (IsLocalRing.maximalIdeal (PRungD.Rm 𝒪 m)).comap
        (TrivSqZeroExt.fstHom (PRungD.Rm 𝒪 m) (PRungD.Rm 𝒪 m) (PRungD.Rm 𝒪 m)) := by
    intro y hy
    rw [Ideal.mem_comap, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
    rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, isUnit_iff_isUnit_fst] at hy
    exact hy
  exact tsze_comap_fst_pow_eq_zero _ m (maximalIdeal_Rm_pow_eq_bot 𝒪 m) z
    (Ideal.pow_right_mono hle (m + 1) hz)

variable {𝒪 m}

theorem apply_eq_zero_of_mem_pow_of_isLocalHom_Am {B : Type} [CommRing B] [IsLocalRing B]
    (f : B →+* PRungD.Am 𝒪 m) [IsLocalHom f] :
    ∀ a ∈ IsLocalRing.maximalIdeal B ^ (m + 1), f a = 0 := by
  intro a ha
  refine eq_zero_of_mem_maximalIdeal_Am_pow 𝒪 m (f a) ?_
  have hmap : (IsLocalRing.maximalIdeal B ^ (m + 1)).map f ≤
      IsLocalRing.maximalIdeal (PRungD.Am 𝒪 m) ^ (m + 1) := by
    rw [Ideal.map_pow]
    exact Ideal.pow_right_mono (Ideal.map_le_iff_le_comap.mpr fun b hb =>
      Ideal.mem_comap.mpr (map_nonunit f b hb)) (m + 1)
  exact hmap (Ideal.mem_map_of_mem f ha)

theorem apply_eq_zero_of_mem_pow_of_isLocalHom_Rm {B : Type} [CommRing B] [IsLocalRing B]
    (f : B →+* PRungD.Rm 𝒪 m) [IsLocalHom f] :
    ∀ a ∈ IsLocalRing.maximalIdeal B ^ m, f a = 0 := by
  intro a ha
  have hmap : (IsLocalRing.maximalIdeal B ^ m).map f ≤ IsLocalRing.maximalIdeal (PRungD.Rm 𝒪 m) ^ m := by
    rw [Ideal.map_pow]
    exact Ideal.pow_right_mono (Ideal.map_le_iff_le_comap.mpr fun b hb =>
      Ideal.mem_comap.mpr (map_nonunit f b hb)) m
  have h := hmap (Ideal.mem_map_of_mem f ha)
  rw [maximalIdeal_Rm_pow_eq_bot] at h
  exact (Submodule.mem_bot _).mp h

end PRungL2.E3Level
p2m_reactivate "P2MW.S_GaloisRep_DeformationRingData_exists_localInvariant_of_ordinaryLine.PRungD P2MW.S_GaloisRep_DeformationRingData_exists_localInvariant_of_ordinaryLine.PRungInvDict"
p2m_reactivate "P2MW.S_GaloisRep_DeformationRingData_exists_localInvariant_of_ordinaryLine.PRungD P2MW.S_GaloisRep_DeformationRingData_exists_localInvariant_of_ordinaryLine.PRungInvDict"

namespace PRungL2
namespace E3Univ

section Mat
variable {A : Type} [CommRing A]

theorem corner_mul (S T : Matrix (Fin 2) (Fin 2) A) :
    (S * T) 0 1 = S 0 0 * T 0 1 + S 0 1 * T 1 1 := by
  simp [Matrix.mul_apply, Fin.sum_univ_two]

theorem det_eq_entry (T : Matrix (Fin 2) (Fin 2) A) (h10 : T 1 0 = 0) (h11 : T 1 1 = 1) :
    T.det = T 0 0 := by
  rw [Matrix.det_fin_two, h10, h11]; ring

theorem conj_corner (S T S' : Matrix (Fin 2) (Fin 2) A) (hT00 : T 0 0 = 1) (hT10 : T 1 0 = 0)
    (hT11 : T 1 1 = 1) (hS'11 : S' 1 1 = 1) (hSS' : S * S' = 1) :
    (S * T * S') 0 1 = S 0 0 * T 0 1 := by
  have h : (S * S') 0 1 = 0 := by rw [hSS']; simp
  simp only [Matrix.mul_apply, Fin.sum_univ_two] at h ⊢
  rw [hT00, hT10, hT11, hS'11] at *
  linear_combination h

theorem entry_eq_of_det_sub_mem (T : Matrix (Fin 2) (Fin 2) A) (a c : A) (hc : c = 0)
    (h : T.det - a ∈ Ideal.span {c}) (h10 : T 1 0 = 0) (h11 : T 1 1 = 1) : T 0 0 = a := by
  rw [hc, Ideal.span_singleton_eq_bot.mpr rfl, Ideal.mem_bot, det_eq_entry T h10 h11,
    sub_eq_zero] at h
  exact h

theorem corner_comm_correction (Λ F : Matrix (Fin 2) (Fin 2) A) (w : A) :
    (Λ + F * Matrix.of ![![0, 0], ![w, 0]] - Matrix.of ![![0, 0], ![w, 0]] * F) 0 1 = Λ 0 1 := by
  simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.vecMul, dotProduct]

end Mat
p2m_reactivate "P2MW.S_GaloisRep_DeformationRingData_exists_localInvariant_of_ordinaryLine.PRungD P2MW.S_GaloisRep_DeformationRingData_exists_localInvariant_of_ordinaryLine.PRungInvDict"

section Finiteness

theorem finite_linearMap {R M N : Type} [Semiring R] [AddCommMonoid M] [Module R M]
    [AddCommMonoid N] [Module R N] [Finite M] [Finite N] : Finite (M →ₗ[R] N) :=
  Finite.of_injective _ DFunLike.coe_injective

theorem finite_linearMap_of_moduleFinite {R M N : Type} [CommRing R] [AddCommGroup M] [Module R M]
    [Module.Finite R M] [AddCommGroup N] [Module R N] [Finite N] : Finite (M →ₗ[R] N) := by
  classical
  obtain ⟨S, hS⟩ := Module.Finite.fg_top (R := R) (M := M)
  refine Finite.of_injective (fun f : M →ₗ[R] N => fun s : (S : Set M) => f s) ?_
  intro f g hfg
  refine LinearMap.ext_on hS fun s hs => ?_
  exact congrFun hfg ⟨s, hs⟩

theorem moduleFinite_cotangent {𝒪 B : Type} [CommRing 𝒪] [CommRing B] [Algebra 𝒪 B]
    [IsNoetherianRing B] (x : B →ₐ[𝒪] 𝒪) :
    Module.Finite 𝒪 (RingHom.ker (x : B →+* 𝒪)).Cotangent := by
  classical
  set I := RingHom.ker (x : B →+* 𝒪) with hI
  haveI : Module.Finite B I := Module.IsNoetherian.finite B I
  haveI : Module.Finite B I.Cotangent := Module.Finite.quotient B _
  obtain ⟨S, hS⟩ := Module.Finite.fg_top (R := B) (M := I.Cotangent)

  have hkill : ∀ (r : B) (v : I.Cotangent), r ∈ I → r • v = 0 := fun r v hr => by
    rw [← algebraMap_smul (B ⧸ I) r v, Ideal.Quotient.algebraMap_eq,
      Ideal.Quotient.eq_zero_iff_mem.mpr hr, zero_smul]
  have hact : ∀ (r : B) (v : I.Cotangent), r • v = x r • v := fun r v => by
    have h : (r - algebraMap 𝒪 B (x r)) • v = 0 := hkill _ v (by
      rw [hI, RingHom.mem_ker, AlgHom.coe_toRingHom]; simp [AlgHom.commutes])
    rwa [sub_smul, algebraMap_smul, sub_eq_zero] at h
  refine ⟨⟨S, ?_⟩⟩
  rw [eq_top_iff]
  rintro v -
  have hv : v ∈ Submodule.span B (S : Set I.Cotangent) := by rw [hS]; trivial
  induction hv using Submodule.span_induction with
  | mem s hs => exact Submodule.subset_span hs
  | zero => exact Submodule.zero_mem _
  | add u w _ _ hu hw => exact Submodule.add_mem _ hu hw
  | smul r u _ hu => rw [hact]; exact Submodule.smul_mem _ _ hu

end Finiteness
p2m_reactivate "P2MW.S_GaloisRep_DeformationRingData_exists_localInvariant_of_ordinaryLine.PRungD P2MW.S_GaloisRep_DeformationRingData_exists_localInvariant_of_ordinaryLine.PRungInvDict"

theorem exists_normalised_root (p : ℕ) (hp : p.Prime) (N : ℕ)
    (P : ValuationSubring (AlgebraicClosure ℚ)) (hP : P.LiesOverPrime p)
    (ϖ : AlgebraicClosure ℚ) (hϖ : ϖ ^ p ^ N = (p : AlgebraicClosure ℚ))
    (x β : AlgebraicClosure ℚ) (hx0 : x ≠ 0) (hxI : ∀ σ ∈ P.inertiaSubgroupIn ℚ, σ x = x)
    (hβ : β ^ p ^ N = x) :
    ∃ (nn : ℕ) (u βt s : AlgebraicClosure ℚ), P.valuation u = 1 ∧
      (∀ σ ∈ P.inertiaSubgroupIn ℚ, σ u = u) ∧ βt ^ p ^ N = u ∧ s ≠ 0 ∧
      (∀ τ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ, τ s = s) ∧ ϖ ^ nn * βt = s * β := by
  have hp0 : (p : AlgebraicClosure ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hp.ne_zero
  have hϖ0 : ϖ ≠ 0 := by
    rintro rfl
    rw [zero_pow (pow_ne_zero _ hp.ne_zero)] at hϖ
    exact hp0 hϖ.symm
  rcases P.mem_or_inv_mem x with hxP | hxP
  ·
    obtain ⟨n, u, hu, huI, hxu⟩ :=
      ValuationSubring.exists_eq_prime_pow_mul_of_forall_mem_inertiaSubgroupIn_apply_eq p hp P hP x
        hx0 hxP hxI
    refine ⟨n, u, β / ϖ ^ n, 1, hu, huI, ?_, one_ne_zero, fun τ => map_one τ, ?_⟩
    · rw [div_pow, ← pow_mul, mul_comm n (p ^ N), pow_mul, hϖ, hβ, hxu,
        mul_div_cancel_left₀ u (pow_ne_zero n hp0)]
    · rw [one_mul, mul_div_assoc', mul_div_cancel_left₀ β (pow_ne_zero _ hϖ0)]
  ·
    have hx0' : x⁻¹ ≠ 0 := inv_ne_zero hx0
    have hxI' : ∀ σ ∈ P.inertiaSubgroupIn ℚ, σ x⁻¹ = x⁻¹ := fun σ hσ => by
      rw [map_inv₀, hxI σ hσ]
    obtain ⟨n, u, hu, huI, hxu⟩ :=
      ValuationSubring.exists_eq_prime_pow_mul_of_forall_mem_inertiaSubgroupIn_apply_eq p hp P hP x⁻¹
        hx0' hxP hxI'
    have hu0 : u ≠ 0 := by
      rintro rfl
      rw [mul_zero] at hxu
      exact hx0' hxu
    have hx : x * (p : AlgebraicClosure ℚ) ^ n = u⁻¹ := by
      rw [← inv_inv x, hxu, mul_inv, mul_comm ((p : AlgebraicClosure ℚ) ^ n)⁻¹, mul_assoc,
        inv_mul_cancel₀ (pow_ne_zero n hp0), mul_one]
    have hle : n ≤ n * p ^ N := Nat.le_mul_of_pos_right n (pow_pos hp.pos N)
    refine ⟨n * p ^ N - n, u⁻¹, β * (p : AlgebraicClosure ℚ) ^ n / ϖ ^ (n * p ^ N - n),
      (p : AlgebraicClosure ℚ) ^ n, by rw [map_inv₀, hu, inv_one],
      fun σ hσ => by rw [map_inv₀, huI σ hσ], ?_, pow_ne_zero n hp0,
      fun τ => by rw [map_pow, map_natCast], ?_⟩
    · rw [div_pow, mul_pow, ← pow_mul (ϖ), mul_comm (n * p ^ N - n) (p ^ N), pow_mul, hϖ, hβ,
        ← pow_mul, show n * p ^ N = (n * p ^ N - n) + n from (Nat.sub_add_cancel hle).symm, pow_add,
        Nat.add_sub_cancel, mul_comm ((p : AlgebraicClosure ℚ) ^ (n * p ^ N - n)), ← mul_assoc,
        mul_div_cancel_right₀ _ (pow_ne_zero _ hp0), hx]
    · rw [mul_div_assoc', mul_div_cancel_left₀ _ (pow_ne_zero _ hϖ0), mul_comm]

end PRungL2.E3Univ
p2m_reactivate "P2MW.S_GaloisRep_DeformationRingData_exists_localInvariant_of_ordinaryLine.PRungD P2MW.S_GaloisRep_DeformationRingData_exists_localInvariant_of_ordinaryLine.PRungInvDict"
p2m_reactivate "P2MW.S_GaloisRep_DeformationRingData_exists_localInvariant_of_ordinaryLine.PRungD P2MW.S_GaloisRep_DeformationRingData_exists_localInvariant_of_ordinaryLine.PRungInvDict"

namespace PRungL2
namespace Holes

open PRungD GaloisRep PRungL2.Setup PRungL2.Obj

theorem exists_universal_kummer_data
    {𝒪 : Type} [CommRing 𝒪] [IsDomain 𝒪] [IsDiscreteValuationRing 𝒪]
    [IsAdicComplete (IsLocalRing.maximalIdeal 𝒪) 𝒪] [Finite (IsLocalRing.ResidueField 𝒪)]
    {ρbar : ResidualGaloisRep (IsLocalRing.ResidueField 𝒪)}
    {𝒟₀ 𝒟' : ∀ ⦃A : Type⦄ [CommRing A] [IsLocalRing A] [Algebra 𝒪 A], GaloisRepAdic A → Prop}
    (D₀ : DeformationRingData 𝒪 ρbar 𝒟₀) (D' : DeformationRingData 𝒪 ρbar 𝒟')
    (θ : D'.R →ₐ[𝒪] D₀.R) (x₀ : D₀.R →ₐ[𝒪] 𝒪)
    (hx₀ : IsLocalHom (x₀ : D₀.R →+* 𝒪)) (hθ : IsLocalHom (θ : D'.R →+* D₀.R))
    (p : ℕ) (hp : p.Prime) (hp2 : p ≠ 2) (hp𝔪 : (p : 𝒪) ∈ IsLocalRing.maximalIdeal 𝒪)
    (P : ValuationSubring (AlgebraicClosure ℚ)) (hP : P.LiesOverPrime p)
    (U U' : Matrix (Fin 2) (Fin 2) 𝒪) (hU'U : U' * U = 1) (hUU' : U * U' = 1)
    (hD : ∀ g ∈ P.decompositionSubgroup ℚ, Fad D₀ D' θ x₀ U U' g 1 0 = 0)
    (hI : ∀ τ ∈ P.inertiaSubgroupIn ℚ, Fad D₀ D' θ x₀ U U' τ 1 0 = 0 ∧ Fad D₀ D' θ x₀ U U' τ 1 1 = 1)
    (hdet : ∀ (g : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (n a : ℕ),
      (∀ μ : AlgebraicClosure ℚ, μ ^ p ^ n = 1 → g μ = μ ^ a) →
        (Fad D₀ D' θ x₀ U U' g).det - (a : 𝒪) ∈ Ideal.span {((p ^ n : ℕ) : 𝒪)})
    (m M : ℕ) [NeZero m] [NeZero M] (hmM : m ≤ M)
    (g₀ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (hg₀ : g₀ ∈ P.inertiaSubgroupIn ℚ)
    (hg₀u : IsUnit (Fadm D₀ D' θ x₀ U U' m g₀ 0 0 - Fadm D₀ D' θ x₀ U U' m g₀ 1 1))
    (hFmul : ∀ (φ : Φ' D₀ D' θ x₀ →ₗ[𝒪] Rm 𝒪 m) (g h : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ),
      Ftil D₀ D' θ x₀ U U' m g₀ φ (g * h) = Ftil D₀ D' θ x₀ U U' m g₀ φ g * Ftil D₀ D' θ x₀ U U' m g₀ φ h)
    (hFone : ∀ φ : Φ' D₀ D' θ x₀ →ₗ[𝒪] Rm 𝒪 m, Ftil D₀ D' θ x₀ U U' m g₀ φ 1 = 1)
    (hF10 : ∀ (φ : Φ' D₀ D' θ x₀ →ₗ[𝒪] Rm 𝒪 m), ∀ g ∈ P.decompositionSubgroup ℚ,
      Ftil D₀ D' θ x₀ U U' m g₀ φ g 1 0 = 0)
    (hF11 : ∀ (φ : Φ' D₀ D' θ x₀ →ₗ[𝒪] Rm 𝒪 m), ∀ τ ∈ P.inertiaSubgroupIn ℚ,
      Ftil D₀ D' θ x₀ U U' m g₀ φ τ 1 1 = 1)
    (hFdet : ∀ (φ : Φ' D₀ D' θ x₀ →ₗ[𝒪] Rm 𝒪 m) (g : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)
      (n a : ℕ), (∀ μ : AlgebraicClosure ℚ, μ ^ p ^ n = 1 → g μ = μ ^ a) →
        (Ftil D₀ D' θ x₀ U U' m g₀ φ g).det - (a : Am 𝒪 m) ∈ Ideal.span {((p ^ n : ℕ) : Am 𝒪 m)})
    (hlev : ∃ L : IntermediateField ℚ (AlgebraicClosure ℚ), FiniteDimensional ℚ L ∧
      (∀ (φ : Φ' D₀ D' θ x₀ →ₗ[𝒪] Rm 𝒪 m) (s : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ),
        (∀ x ∈ L, s x = x) → Ftil D₀ D' θ x₀ U U' m g₀ φ s = 1) ∧
      (∀ s : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ, (∀ x ∈ L, s x = x) →
        Fadm D₀ D' θ x₀ U U' M s = 1))
    [Finite (Rm 𝒪 M)] [Finite (Rm 𝒪 m)] [Finite (Φ' D₀ D' θ x₀ →ₗ[𝒪] Rm 𝒪 m)] :
    ∃ (N : ℕ) (_ : M ≤ N) (ζ ϖ : AlgebraicClosure ℚ) (_ : IsPrimitiveRoot ζ (p ^ N))
      (_ : ϖ ^ p ^ N = (p : AlgebraicClosure ℚ))
      (t : ℕ) (nn : Fin t → ℕ) (u βt : Fin t → AlgebraicClosure ℚ)
      (a : Fin t → Rm 𝒪 M × ((Φ' D₀ D' θ x₀ →ₗ[𝒪] Rm 𝒪 m) →ₗ[𝒪] Rm 𝒪 m)),
      (∀ i, P.valuation (u i) = 1) ∧ (∀ i, ∀ σ ∈ P.inertiaSubgroupIn ℚ, σ (u i) = u i) ∧
      (∀ i, βt i ^ p ^ N = u i) ∧
      (∀ (φ : Φ' D₀ D' θ x₀ →ₗ[𝒪] Rm 𝒪 m), ∀ τ ∈ P.inertiaSubgroupIn ℚ,
        (∀ ξ : AlgebraicClosure ℚ, ξ ^ p ^ N = 1 → τ ξ = ξ) →
        ∀ k : Fin t → ℕ, (∀ i, τ (ϖ ^ nn i * βt i) = ζ ^ (k i) * (ϖ ^ nn i * βt i)) →
          Ftil D₀ D' θ x₀ U U' m g₀ φ τ 0 1 = ∑ i, (k i) • evφ D₀ D' θ x₀ hmM φ (a i)) ∧
      (∀ τ ∈ P.inertiaSubgroupIn ℚ,
        (∀ ξ : AlgebraicClosure ℚ, ξ ^ p ^ N = 1 → τ ξ = ξ) →
        ∀ k : Fin t → ℕ, (∀ i, τ (ϖ ^ nn i * βt i) = ζ ^ (k i) * (ϖ ^ nn i * βt i)) →
          Fadm D₀ D' θ x₀ U U' M τ 0 1 = ∑ i, (k i) • (a i).1) := by
  classical
  haveI hxP := isLocalHom_xPrime D₀ D' θ x₀ hx₀ hθ
  have hID : P.inertiaSubgroupIn ℚ ≤ P.decompositionSubgroup ℚ := Subgroup.map_subtype_le _
  have hp0 : p ≠ 0 := hp.ne_zero
  haveI : NeZero (p ^ M) := ⟨pow_ne_zero _ hp0⟩

  obtain ⟨ζ, hζ⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot (AlgebraicClosure ℚ) (p ^ M)
  obtain ⟨ϖ, hϖ⟩ := IsAlgClosed.exists_pow_nat_eq (p : AlgebraicClosure ℚ) (pow_pos hp.pos M)

  have hpOM : (p : 𝒪) ^ M ∈ IsLocalRing.maximalIdeal 𝒪 ^ M := Ideal.pow_mem_pow hp𝔪 M
  have hpM : ((p ^ M : ℕ) : Rm 𝒪 M) = 0 := by
    rw [Nat.cast_pow, ← map_natCast (Ideal.Quotient.mk (IsLocalRing.maximalIdeal 𝒪 ^ M)), ← map_pow,
      Ideal.Quotient.eq_zero_iff_mem]
    exact hpOM
  have hpm : ((p ^ M : ℕ) : Rm 𝒪 m) = 0 := by
    rw [Nat.cast_pow, ← map_natCast (Ideal.Quotient.mk (IsLocalRing.maximalIdeal 𝒪 ^ m)), ← map_pow,
      Ideal.Quotient.eq_zero_iff_mem]
    exact Ideal.pow_le_pow_right hmM hpOM
  have hpAm : ((p ^ M : ℕ) : Am 𝒪 m) = 0 :=
    TrivSqZeroExt.ext (by rw [TrivSqZeroExt.fst_natCast, hpm, TrivSqZeroExt.fst_zero])
      (by rw [TrivSqZeroExt.snd_natCast, TrivSqZeroExt.snd_zero])

  have hacts1 : ∀ τ : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ), (∀ ξ : AlgebraicClosure ℚ, ξ ^ p ^ M = 1 → τ ξ = ξ) →
      ∀ μ : AlgebraicClosure ℚ, μ ^ p ^ M = 1 → τ μ = μ ^ 1 := fun τ h μ hμ => by
    rw [pow_one]; exact h μ hμ
  have hactsζ : ∀ (σ : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)) (a : ℕ), σ ζ = ζ ^ a →
      ∀ μ : AlgebraicClosure ℚ, μ ^ p ^ M = 1 → σ μ = μ ^ a := fun σ a ha μ hμ => by
    obtain ⟨j, -, rfl⟩ := hζ.eq_pow_of_pow_eq_one hμ
    rw [map_pow, ha, ← pow_mul, ← pow_mul, mul_comm]

  have PM10 : ∀ τ ∈ P.inertiaSubgroupIn ℚ, Fadm D₀ D' θ x₀ U U' M τ 1 0 = 0 := fun τ hτ => by
    simp only [Fadm, Matrix.map_apply, (hI τ hτ).1, map_zero]
  have PM11 : ∀ τ ∈ P.inertiaSubgroupIn ℚ, Fadm D₀ D' θ x₀ U U' M τ 1 1 = 1 := fun τ hτ => by
    simp only [Fadm, Matrix.map_apply, (hI τ hτ).2, map_one]
  have PMdet : ∀ (g : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)) (n a : ℕ), (∀ μ : AlgebraicClosure ℚ, μ ^ p ^ n = 1 → g μ = μ ^ a) →
      (Fadm D₀ D' θ x₀ U U' M g).det - (a : Rm 𝒪 M) ∈ Ideal.span {((p ^ n : ℕ) : Rm 𝒪 M)} := by
    intro g n a hg
    have h := Ideal.mem_map_of_mem (algebraMap 𝒪 (Rm 𝒪 M)) (hdet g n a hg)
    rw [Ideal.map_span, Set.image_singleton, map_sub, map_natCast, map_natCast, RingHom.map_det] at h
    exact h
  have PM00 : ∀ σ ∈ P.inertiaSubgroupIn ℚ, ∀ a : ℕ,
      (∀ μ : AlgebraicClosure ℚ, μ ^ p ^ M = 1 → σ μ = μ ^ a) → Fadm D₀ D' θ x₀ U U' M σ 0 0 = (a : Rm 𝒪 M) :=
    fun σ hσ a ha => PRungL2.E3Univ.entry_eq_of_det_sub_mem _ _ _ hpM (PMdet σ M a ha) (PM10 σ hσ) (PM11 σ hσ)
  have PMmul := fun g h : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) => Fadm_mul D₀ D' θ x₀ U U' M hUU' g h
  have PMinv : ∀ σ : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ), Fadm D₀ D' θ x₀ U U' M σ * Fadm D₀ D' θ x₀ U U' M σ⁻¹ = 1 := fun σ => by
    rw [← PMmul, mul_inv_cancel, Fadm_one D₀ D' θ x₀ U U' M hU'U]

  have T10 : ∀ (φ : (Φ' D₀ D' θ x₀ →ₗ[𝒪] Rm 𝒪 m)), ∀ τ ∈ P.inertiaSubgroupIn ℚ, Ftil D₀ D' θ x₀ U U' m g₀ φ τ 1 0 = 0 :=
    fun φ τ hτ => hF10 φ τ (hID hτ)
  have T00 : ∀ (φ : (Φ' D₀ D' θ x₀ →ₗ[𝒪] Rm 𝒪 m)), ∀ σ ∈ P.inertiaSubgroupIn ℚ, ∀ a : ℕ,
      (∀ μ : AlgebraicClosure ℚ, μ ^ p ^ M = 1 → σ μ = μ ^ a) → Ftil D₀ D' θ x₀ U U' m g₀ φ σ 0 0 = (a : Am 𝒪 m) :=
    fun φ σ hσ a ha =>
      PRungL2.E3Univ.entry_eq_of_det_sub_mem _ _ _ hpAm (hFdet φ σ M a ha) (T10 φ σ hσ) (hF11 φ σ hσ)
  have Tinv : ∀ (φ : (Φ' D₀ D' θ x₀ →ₗ[𝒪] Rm 𝒪 m)) (σ : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)), Ftil D₀ D' θ x₀ U U' m g₀ φ σ * Ftil D₀ D' θ x₀ U U' m g₀ φ σ⁻¹ = 1 := fun φ σ => by
    rw [← hFmul, mul_inv_cancel, hFone]

  have T01 : ∀ (φ : (Φ' D₀ D' θ x₀ →ₗ[𝒪] Rm 𝒪 m)) (g : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)), Ftil D₀ D' θ x₀ U U' m g₀ φ g 0 1 =
      TrivSqZeroExt.inl (Fadm D₀ D' θ x₀ U U' m g 0 1) + TrivSqZeroExt.inr (Lam D₀ D' θ x₀ U U' m φ g 0 1) := by
    intro φ g
    rw [show Ftil D₀ D' θ x₀ U U' m g₀ φ g = (Fadm D₀ D' θ x₀ U U' m g).map TrivSqZeroExt.inl +
      (LamT D₀ D' θ x₀ U U' m g₀ φ g).map TrivSqZeroExt.inr from rfl, Matrix.add_apply, Matrix.map_apply,
      Matrix.map_apply, show LamT D₀ D' θ x₀ U U' m g₀ φ g = Lam D₀ D' θ x₀ U U' m φ g + Fadm D₀ D' θ x₀ U U' m g * Nmat D₀ D' θ x₀ U U' m g₀ φ -
        Nmat D₀ D' θ x₀ U U' m g₀ φ * Fadm D₀ D' θ x₀ U U' m g from rfl,
      show Nmat D₀ D' θ x₀ U U' m g₀ φ = Matrix.of ![![0, 0], ![w₁ D₀ D' θ x₀ U U' m g₀ φ, 0]] from rfl,
      PRungL2.E3Univ.corner_comm_correction]
  have T01snd : ∀ (φ : (Φ' D₀ D' θ x₀ →ₗ[𝒪] Rm 𝒪 m)) (g : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)), (Ftil D₀ D' θ x₀ U U' m g₀ φ g 0 1).snd = Lam D₀ D' θ x₀ U U' m φ g 0 1 := fun φ g => by
    rw [T01, TrivSqZeroExt.snd_add, TrivSqZeroExt.snd_inl, TrivSqZeroExt.snd_inr, zero_add]
  have T01fst : ∀ (φ : (Φ' D₀ D' θ x₀ →ₗ[𝒪] Rm 𝒪 m)) (g : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)), (Ftil D₀ D' θ x₀ U U' m g₀ φ g 0 1).fst = Fadm D₀ D' θ x₀ U U' m g 0 1 := fun φ g => by
    rw [T01, TrivSqZeroExt.fst_add, TrivSqZeroExt.fst_inl, TrivSqZeroExt.fst_inr, add_zero]

  let cor : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) → ((Φ' D₀ D' θ x₀ →ₗ[𝒪] Rm 𝒪 m) →ₗ[𝒪] Rm 𝒪 m) := fun τ =>
    { toFun := fun φ => Lam D₀ D' θ x₀ U U' m φ τ 0 1
      map_add' := fun φ ψ => by rw [map_add, Pi.add_apply, Matrix.add_apply]
      map_smul' := fun c φ => by rw [map_smul, Pi.smul_apply, Matrix.smul_apply, RingHom.id_apply] }
  have cor_apply : ∀ (τ : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)) (φ : (Φ' D₀ D' θ x₀ →ₗ[𝒪] Rm 𝒪 m)), cor τ φ = Lam D₀ D' θ x₀ U U' m φ τ 0 1 := fun _ _ => rfl
  let C : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) → (Rm 𝒪 M × ((Φ' D₀ D' θ x₀ →ₗ[𝒪] Rm 𝒪 m) →ₗ[𝒪] Rm 𝒪 m)) := fun τ => (Fadm D₀ D' θ x₀ U U' M τ 0 1, cor τ)
  have C1 : ∀ τ : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ), (C τ).1 = Fadm D₀ D' θ x₀ U U' M τ 0 1 := fun _ => rfl
  have C2 : ∀ (τ : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)) (φ : (Φ' D₀ D' θ x₀ →ₗ[𝒪] Rm 𝒪 m)), (C τ).2 φ = Lam D₀ D' θ x₀ U U' m φ τ 0 1 := fun _ _ => rfl

  haveI : Finite ((Φ' D₀ D' θ x₀ →ₗ[𝒪] Rm 𝒪 m) →ₗ[𝒪] Rm 𝒪 m) := PRungL2.E3Univ.finite_linearMap
  have hM' : ∀ z : (Rm 𝒪 M × ((Φ' D₀ D' θ x₀ →ₗ[𝒪] Rm 𝒪 m) →ₗ[𝒪] Rm 𝒪 m)), (p ^ M) • z = 0 := by
    intro z
    refine Prod.ext ?_ ?_
    · show (p ^ M) • z.1 = 0
      rw [nsmul_eq_mul, hpM, zero_mul]
    · show (p ^ M) • z.2 = 0
      refine LinearMap.ext fun φ => ?_
      change (p ^ M) • z.2 φ = 0
      rw [nsmul_eq_mul, hpm, zero_mul]

  have hlev' : ∃ F : IntermediateField ℚ (AlgebraicClosure ℚ), FiniteDimensional ℚ F ∧
      ∀ τ ∈ P.inertiaSubgroupIn ℚ, ∀ s ∈ P.inertiaSubgroupIn ℚ, s ∈ F.fixingSubgroup → C (τ * s) = C τ := by
    obtain ⟨L, hL, hT, hF⟩ := hlev
    refine ⟨L, hL, fun τ _ s _ hs => ?_⟩
    rw [IntermediateField.mem_fixingSubgroup_iff] at hs
    refine Prod.ext ?_ (LinearMap.ext fun φ => ?_)
    · show Fadm D₀ D' θ x₀ U U' M (τ * s) 0 1 = Fadm D₀ D' θ x₀ U U' M τ 0 1
      rw [PMmul, hF s hs, mul_one]
    · show Lam D₀ D' θ x₀ U U' m φ (τ * s) 0 1 = Lam D₀ D' θ x₀ U U' m φ τ 0 1
      rw [← T01snd, ← T01snd, hFmul, hT φ s hs, mul_one]

  have hadd' : ∀ τ ∈ P.inertiaSubgroupIn ℚ, ∀ τ' ∈ P.inertiaSubgroupIn ℚ,
      (∀ ξ : AlgebraicClosure ℚ, ξ ^ p ^ M = 1 → τ ξ = ξ) →
      (∀ ξ : AlgebraicClosure ℚ, ξ ^ p ^ M = 1 → τ' ξ = ξ) → C (τ * τ') = C τ + C τ' := by
    intro τ hτ τ' hτ' h1 h2
    refine Prod.ext ?_ (LinearMap.ext fun φ => ?_)
    · show Fadm D₀ D' θ x₀ U U' M (τ * τ') 0 1 = Fadm D₀ D' θ x₀ U U' M τ 0 1 + Fadm D₀ D' θ x₀ U U' M τ' 0 1
      rw [PMmul, PRungL2.E3Univ.corner_mul, PM00 τ hτ 1 (hacts1 τ h1), PM11 τ' hτ', Nat.cast_one, one_mul,
        mul_one, add_comm]
    · show Lam D₀ D' θ x₀ U U' m φ (τ * τ') 0 1 = Lam D₀ D' θ x₀ U U' m φ τ 0 1 + Lam D₀ D' θ x₀ U U' m φ τ' 0 1
      rw [← T01snd, ← T01snd, ← T01snd, hFmul, PRungL2.E3Univ.corner_mul, T00 φ τ hτ 1 (hacts1 τ h1),
        hF11 φ τ' hτ', Nat.cast_one, one_mul, mul_one, TrivSqZeroExt.snd_add, add_comm]

  have hconj' : ∀ σ ∈ P.inertiaSubgroupIn ℚ, ∀ a : ℕ, σ ζ = ζ ^ a →
      ∀ τ ∈ P.inertiaSubgroupIn ℚ, (∀ ξ : AlgebraicClosure ℚ, ξ ^ p ^ M = 1 → τ ξ = ξ) →
        C (σ * τ * σ⁻¹) = a • C τ := by
    intro σ hσ a ha τ hτ h1
    have hσ' : σ⁻¹ ∈ P.inertiaSubgroupIn ℚ := Subgroup.inv_mem _ hσ
    refine Prod.ext ?_ (LinearMap.ext fun φ => ?_)
    · show Fadm D₀ D' θ x₀ U U' M (σ * τ * σ⁻¹) 0 1 = (a • C τ).1
      rw [Prod.smul_fst, C1, PMmul, PMmul, PRungL2.E3Univ.conj_corner _ _ _ (PM00 τ hτ 1 (hacts1 τ h1) ▸ Nat.cast_one)
        (PM10 τ hτ) (PM11 τ hτ) (PM11 σ⁻¹ hσ') (PMinv σ), PM00 σ hσ a (hactsζ σ a ha), nsmul_eq_mul]
    · change Lam D₀ D' θ x₀ U U' m φ (σ * τ * σ⁻¹) 0 1 = a • Lam D₀ D' θ x₀ U U' m φ τ 0 1
      rw [← T01snd, hFmul, hFmul,
        PRungL2.E3Univ.conj_corner _ _ _ ((T00 φ τ hτ 1 (hacts1 τ h1)).trans Nat.cast_one) (T10 φ τ hτ)
          (hF11 φ τ hτ) (hF11 φ σ⁻¹ hσ') (Tinv φ σ),
        T00 φ σ hσ a (hactsζ σ a ha), TrivSqZeroExt.snd_mul, TrivSqZeroExt.fst_natCast,
        TrivSqZeroExt.snd_natCast, smul_zero, add_zero, T01snd, smul_eq_mul, nsmul_eq_mul]

  obtain ⟨t, x, β, a, hx0, hxI, hβ, hdec⟩ :=
    ValuationSubring.exists_kummer_decomposition_of_inertia_cocycle p hp hp2 M P hP ζ hζ hM' C hlev'
      hadd' hconj'

  choose nn u βt s hu huI hβt hs0 hsfix hsβ using fun i =>
    PRungL2.E3Univ.exists_normalised_root p hp M P hP ϖ hϖ (x i) (β i) (hx0 i) (hxI i) (hβ i)

  have hback : ∀ (τ : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)) (k : Fin t → ℕ),
      (∀ i, τ (ϖ ^ nn i * βt i) = ζ ^ (k i) * (ϖ ^ nn i * βt i)) → ∀ i, τ (β i) = ζ ^ (k i) * β i := by
    intro τ k hk i
    have h := hk i
    rw [hsβ i, map_mul, hsfix i τ, mul_left_comm] at h
    exact mul_left_cancel₀ (hs0 i) h

  have hev : ∀ (φ : (Φ' D₀ D' θ x₀ →ₗ[𝒪] Rm 𝒪 m)) (k : Fin t → ℕ),
      evφ D₀ D' θ x₀ hmM φ (∑ i, k i • a i) = ∑ i, k i • evφ D₀ D' θ x₀ hmM φ (a i) := by
    intro φ k
    rw [map_sum]
    exact Finset.sum_congr rfl fun i _ => map_nsmul _ _ _

  have hevC : ∀ (φ : (Φ' D₀ D' θ x₀ →ₗ[𝒪] Rm 𝒪 m)) (τ : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)), evφ D₀ D' θ x₀ hmM φ (C τ) = Ftil D₀ D' θ x₀ U U' m g₀ φ τ 0 1 := by
    intro φ τ
    show TrivSqZeroExt.inl (red 𝒪 hmM (Fadm D₀ D' θ x₀ U U' M τ 0 1)) + TrivSqZeroExt.inr (Lam D₀ D' θ x₀ U U' m φ τ 0 1) = _
    rw [T01]
    congr 2
  refine ⟨M, le_rfl, ζ, ϖ, hζ, hϖ, t, nn, u, βt, a, hu, huI, hβt, ?_, ?_⟩
  · intro φ τ hτ hfix k hk
    rw [← hevC, hdec τ hτ hfix k (hback τ k hk), hev]
  · intro τ hτ hfix k hk
    rw [← C1, hdec τ hτ hfix k (hback τ k hk), Prod.fst_sum]
    exact Finset.sum_congr rfl fun i _ => Prod.smul_fst _ _

end PRungL2.Holes
p2m_reactivate "P2MW.S_GaloisRep_DeformationRingData_exists_localInvariant_of_ordinaryLine.PRungD P2MW.S_GaloisRep_DeformationRingData_exists_localInvariant_of_ordinaryLine.PRungInvDict"
p2m_reactivate "P2MW.S_GaloisRep_DeformationRingData_exists_localInvariant_of_ordinaryLine.PRungD P2MW.S_GaloisRep_DeformationRingData_exists_localInvariant_of_ordinaryLine.PRungInvDict"

namespace PRungL2
namespace E3Disc

open PRungD GaloisRep PRungL2.Setup PRungL2.Obj

theorem map_toMatrix_eq_one_of_baseChangeAlong_apply_eq_one
    {A B : Type} [CommRing A] [IsLocalRing A] [CommRing B] [IsLocalRing B]
    (ρ : GaloisRepAdic A) (b : Module.Basis (Fin 2) A ρ.V) (f : A →+* B) (hf : IsLocalHom f)
    (g : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (h : (ρ.baseChangeAlong f hf).ρ g = 1) :
    (LinearMap.toMatrix b b (ρ.ρ g)).map f = 1 := by
  letI : Algebra A B := f.toAlgebra
  have e : (LinearMap.toMatrix b b (ρ.ρ g)).map f =
      LinearMap.toMatrix (Algebra.TensorProduct.basis B b) (Algebra.TensorProduct.basis B b)
        ((ρ.ρ g).baseChange B) := by
    rw [LinearMap.toMatrix_baseChange, RingHom.algebraMap_toAlgebra]
  rw [e, show (ρ.ρ g).baseChange B = (ρ.baseChangeAlong f hf).ρ g from rfl, h]
  exact LinearMap.toMatrix_one _

variable {𝒪 : Type} [CommRing 𝒪] [IsDomain 𝒪] [IsDiscreteValuationRing 𝒪]
  [IsAdicComplete (IsLocalRing.maximalIdeal 𝒪) 𝒪]
  {ρbar : ResidualGaloisRep (IsLocalRing.ResidueField 𝒪)}
  {𝒟₀ 𝒟' : ∀ ⦃A : Type⦄ [CommRing A] [IsLocalRing A] [Algebra 𝒪 A], GaloisRepAdic A → Prop}
  (D₀ : DeformationRingData 𝒪 ρbar 𝒟₀) (D' : DeformationRingData 𝒪 ρbar 𝒟')
  (θ : D'.R →ₐ[𝒪] D₀.R) (x₀ : D₀.R →ₐ[𝒪] 𝒪)
  (hx₀ : IsLocalHom (x₀ : D₀.R →+* 𝒪)) (hθ : IsLocalHom (θ : D'.R →+* D₀.R))
  (U U' : Matrix (Fin 2) (Fin 2) 𝒪) (hU'U : U' * U = 1)
  (m M : ℕ) [NeZero m] [NeZero M] (hmM : m ≤ M)
  (g₀ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)

include hU'U hmM in

theorem hlev_discharge
    (hlink : ∀ φ : Φ' D₀ D' θ x₀ →ₗ[𝒪] Rm 𝒪 m,
      haveI := isLocalHom_xPrime D₀ D' θ x₀ hx₀ hθ
      ∃ cA : Module.Basis (Fin 2) (Am 𝒪 m) (D'.ρ.baseChangeAlong (xOfCotangentHom (xPrime D₀ D' θ x₀) φ : D'.R →+* Am 𝒪 m)
          (isLocalHom_xOfCotangentHom (xPrime D₀ D' θ x₀) φ)).V,
        ∀ g : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ,
          LinearMap.toMatrix cA cA ((D'.ρ.baseChangeAlong (xOfCotangentHom (xPrime D₀ D' θ x₀) φ : D'.R →+* Am 𝒪 m)
          (isLocalHom_xOfCotangentHom (xPrime D₀ D' θ x₀) φ)).ρ g) =
          (Fadm D₀ D' θ x₀ U U' m g).map TrivSqZeroExt.inl +
            (Lam D₀ D' θ x₀ U U' m φ g).map TrivSqZeroExt.inr) :
    ∃ L : IntermediateField ℚ (AlgebraicClosure ℚ), FiniteDimensional ℚ L ∧
      (∀ (φ : Φ' D₀ D' θ x₀ →ₗ[𝒪] Rm 𝒪 m) (s : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ),
        (∀ x ∈ L, s x = x) → Ftil D₀ D' θ x₀ U U' m g₀ φ s = 1) ∧
      (∀ s : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ, (∀ x ∈ L, s x = x) →
        Fadm D₀ D' θ x₀ U U' M s = 1) := by
  classical
  haveI hxP := isLocalHom_xPrime D₀ D' θ x₀ hx₀ hθ
  obtain ⟨L, hL, hlev⟩ := GaloisRepAdic.exists_level_forall_baseChangeAlong_apply_eq_one D'.ρ (M + 1)
  refine ⟨L, hL, fun φ s hs => ?_, fun s hs => ?_⟩
  ·
    haveI := isLocalHom_xOfCotangentHom (xPrime D₀ D' θ x₀) φ
    have hkill : ∀ a ∈ IsLocalRing.maximalIdeal D'.R ^ (M + 1),
        (xOfCotangentHom (xPrime D₀ D' θ x₀) φ : D'.R →+* Am 𝒪 m) a = 0 := fun a ha =>
      PRungL2.E3Level.apply_eq_zero_of_mem_pow_of_isLocalHom_Am _ a
        (Ideal.pow_le_pow_right (Nat.succ_le_succ hmM) ha)
    have h1 := hlev _ (isLocalHom_xOfCotangentHom (xPrime D₀ D' θ x₀) φ) hkill s hs
    obtain ⟨cA, hcA⟩ := hlink φ
    have hmat := hcA s
    rw [h1, LinearMap.toMatrix_one] at hmat

    have hF : Fadm D₀ D' θ x₀ U U' m s = 1 := by
      ext i j
      have h := congrArg TrivSqZeroExt.fst (congrFun (congrFun hmat i) j)
      rw [Matrix.add_apply, Matrix.map_apply, Matrix.map_apply, TrivSqZeroExt.fst_add,
        TrivSqZeroExt.fst_inl, TrivSqZeroExt.fst_inr, add_zero] at h
      rw [← h, Matrix.one_apply, Matrix.one_apply]
      split_ifs <;> rfl
    have hΛ : Lam D₀ D' θ x₀ U U' m φ s = 0 := by
      ext i j
      have h := congrArg TrivSqZeroExt.snd (congrFun (congrFun hmat i) j)
      rw [Matrix.add_apply, Matrix.map_apply, Matrix.map_apply, TrivSqZeroExt.snd_add,
        TrivSqZeroExt.snd_inl, TrivSqZeroExt.snd_inr, zero_add] at h
      rw [← h, Matrix.zero_apply, Matrix.one_apply]
      split_ifs <;> rfl
    show (Fadm D₀ D' θ x₀ U U' m s).map TrivSqZeroExt.inl +
      (Lam D₀ D' θ x₀ U U' m φ s + Fadm D₀ D' θ x₀ U U' m s * Nmat D₀ D' θ x₀ U U' m g₀ φ -
        Nmat D₀ D' θ x₀ U U' m g₀ φ * Fadm D₀ D' θ x₀ U U' m s).map TrivSqZeroExt.inr = 1
    rw [hF, hΛ, zero_add, one_mul, mul_one, sub_self,
      Matrix.map_one _ (TrivSqZeroExt.inl_zero _) (TrivSqZeroExt.inl_one _),
      Matrix.map_zero _ (TrivSqZeroExt.inr_zero _), add_zero]
  ·
    set f : D'.R →+* Rm 𝒪 M := (algebraMap 𝒪 (Rm 𝒪 M)).comp (xPrime D₀ D' θ x₀ : D'.R →+* 𝒪) with hf
    haveI hfl : IsLocalHom f := RingHom.isLocalHom_comp _ _
    have hkill : ∀ a ∈ IsLocalRing.maximalIdeal D'.R ^ (M + 1), f a = 0 := fun a ha =>
      PRungL2.E3Level.apply_eq_zero_of_mem_pow_of_isLocalHom_Rm f a
        (Ideal.pow_le_pow_right (Nat.le_succ M) ha)
    have h1 := hlev f hfl hkill s hs
    have hM := map_toMatrix_eq_one_of_baseChangeAlong_apply_eq_one D'.ρ (bD D') f hfl s h1
    show (U' * Mof D₀ D' θ x₀ s * U).map (algebraMap 𝒪 (Rm 𝒪 M)) = 1
    rw [Matrix.map_mul, Matrix.map_mul, show (Mof D₀ D' θ x₀ s).map (algebraMap 𝒪 (Rm 𝒪 M)) = 1 from by
      rw [show Mof D₀ D' θ x₀ s = (LinearMap.toMatrix (bD D') (bD D') (D'.ρ.ρ s)).map
        (xPrime D₀ D' θ x₀ : D'.R →+* 𝒪) from rfl, Matrix.map_map]; exact hM,
      mul_one, ← Matrix.map_mul, hU'U, Matrix.map_one _ (map_zero _) (map_one _)]

end PRungL2.E3Disc
p2m_reactivate "P2MW.S_GaloisRep_DeformationRingData_exists_localInvariant_of_ordinaryLine.PRungD P2MW.S_GaloisRep_DeformationRingData_exists_localInvariant_of_ordinaryLine.PRungInvDict"
p2m_reactivate "P2MW.S_GaloisRep_DeformationRingData_exists_localInvariant_of_ordinaryLine.PRungD P2MW.S_GaloisRep_DeformationRingData_exists_localInvariant_of_ordinaryLine.PRungInvDict"

namespace PRungL2
namespace Holes

open PRungD GaloisRep PRungL2.Setup PRungL2.Obj

theorem mem_ker_lcomp_of_isOfType_dualNumberLift
    {𝒪 : Type} [CommRing 𝒪] [IsDomain 𝒪] [IsDiscreteValuationRing 𝒪]
    [IsAdicComplete (IsLocalRing.maximalIdeal 𝒪) 𝒪]
    {ρbar : ResidualGaloisRep (IsLocalRing.ResidueField 𝒪)}
    {𝒟₀ 𝒟' : ∀ ⦃A : Type⦄ [CommRing A] [IsLocalRing A] [Algebra 𝒪 A], GaloisRepAdic A → Prop}
    (D₀ : GaloisRep.DeformationRingData 𝒪 ρbar 𝒟₀) (D' : GaloisRep.DeformationRingData 𝒪 ρbar 𝒟')
    (θ : D'.R →ₐ[𝒪] D₀.R) (x₀ : D₀.R →ₐ[𝒪] 𝒪)
    (hθ : IsLocalHom (θ : D'.R →+* D₀.R)) (hx₀ : IsLocalHom (x₀ : D₀.R →+* 𝒪))
    (hθρ : (D'.ρ.baseChangeAlong (θ : D'.R →+* D₀.R) hθ).IsEquiv D₀.ρ)
    (hθsurj : Function.Surjective θ)
    (H1 : ∀ {A : Type} [CommRing A] [IsLocalRing A] [Algebra 𝒪 A] (ρA : GaloisRepAdic A)
        {B : Type} [CommRing B] [IsLocalRing B] [Algebra 𝒪 B] (f : A →+* B) (hf : IsLocalHom f),
      𝒟' ρA → 𝒟' (ρA.baseChangeAlong f hf))
    (m : ℕ) [NeZero m]
    (φ : PRungD.Φ' D₀ D' θ x₀ →ₗ[𝒪] PRungD.Rm 𝒪 m)
    (h𝒟₀ : haveI := PRungD.isLocalHom_xPrime D₀ D' θ x₀ hx₀ hθ
      𝒟₀ (D'.ρ.baseChangeAlong
        (PRungD.xOfCotangentHom (PRungD.xPrime D₀ D' θ x₀) φ : D'.R →+* PRungD.Am 𝒪 m)
        (PRungD.isLocalHom_xOfCotangentHom (PRungD.xPrime D₀ D' θ x₀) φ))) :
    φ ∈ LinearMap.ker (LinearMap.lcomp 𝒪 (PRungD.Rm 𝒪 m)
        (LinearMap.ker (Ideal.mapCotangent (RingHom.ker (x₀.comp θ : D'.R →ₐ[𝒪] 𝒪))
            (RingHom.ker x₀) θ (fun _ hr => hr))).subtype) := by
  haveI := PRungD.isLocalHom_xPrime D₀ D' θ x₀ hx₀ hθ
  have h := GaloisRep.DeformationRingData.comp_subtype_ker_mapCotangent_eq_zero_of_isOfType_lift D₀
    D' θ hθ hθρ hθsurj x₀ (PRungD.Rm 𝒪 m) (PRungD.residue_surjective_Am 𝒪 m) φ
    (PRungD.xOfCotangentHom (PRungD.xPrime D₀ D' θ x₀) φ)
    (PRungD.isLocalHom_xOfCotangentHom (PRungD.xPrime D₀ D' θ x₀) φ)
    (fun r hr => by
      have e2 : (⟨r, hr⟩ : (RingHom.ker (x₀.comp θ : D'.R →ₐ[𝒪] 𝒪))) = PRungD.δ (PRungD.xPrime D₀ D' θ x₀) r :=
        Subtype.ext (by
          rw [PRungD.coe_δ, show PRungD.xPrime D₀ D' θ x₀ r = 0 from hr, map_zero, sub_zero])
      rw [e2]
      rfl)
    (H1 _ _ _ D'.isOfType) h𝒟₀
  exact (LinearMap.mem_ker (f := LinearMap.lcomp 𝒪 (PRungD.Rm 𝒪 m)
    (LinearMap.ker (Ideal.mapCotangent (RingHom.ker (x₀.comp θ : D'.R →ₐ[𝒪] 𝒪)) (RingHom.ker x₀) θ (fun _ hr => hr))).subtype)).mpr h

set_option maxHeartbeats 3200000 in

theorem exists_local_invariant
    {𝒪 : Type} [CommRing 𝒪] [IsDomain 𝒪] [IsDiscreteValuationRing 𝒪]
    [IsAdicComplete (IsLocalRing.maximalIdeal 𝒪) 𝒪]
    {ρbar : ResidualGaloisRep (IsLocalRing.ResidueField 𝒪)}
    {𝒟₀ 𝒟' : ∀ ⦃A : Type⦄ [CommRing A] [IsLocalRing A] [Algebra 𝒪 A], GaloisRepAdic A → Prop}
    (D₀ : GaloisRep.DeformationRingData 𝒪 ρbar 𝒟₀) (D' : GaloisRep.DeformationRingData 𝒪 ρbar 𝒟')
    (θ : D'.R →ₐ[𝒪] D₀.R) (x₀ : D₀.R →ₐ[𝒪] 𝒪)
    (p : ℕ) (hp : p.Prime) (hp2 : p ≠ 2)
    (hp𝔪 : (p : 𝒪) ∈ IsLocalRing.maximalIdeal 𝒪)
    (hθ : IsLocalHom (θ : D'.R →+* D₀.R)) (hx₀ : IsLocalHom (x₀ : D₀.R →+* 𝒪))
    (hfl : (D₀.ρ.baseChangeAlong (x₀ : D₀.R →+* 𝒪) hx₀).IsFlatAt p)
    (hθρ : (D'.ρ.baseChangeAlong (θ : D'.R →+* D₀.R) hθ).IsEquiv D₀.ρ)
    (hθsurj : Function.Surjective θ)
    (P : ValuationSubring (AlgebraicClosure ℚ)) (hP : P.LiesOverPrime p)
    (L : Submodule 𝒪 (D₀.ρ.baseChangeAlong (x₀ : D₀.R →+* 𝒪) hx₀).V)
    (hLb : ∃ b : Module.Basis (Fin 2) 𝒪 (D₀.ρ.baseChangeAlong (x₀ : D₀.R →+* 𝒪) hx₀).V, L = 𝒪 ∙ b 0)
    (hLD : ∀ σ ∈ P.decompositionSubgroup ℚ, ∀ v ∈ L,
      (D₀.ρ.baseChangeAlong (x₀ : D₀.R →+* 𝒪) hx₀).ρ σ v ∈ L)
    (hLI : ∀ σ ∈ P.inertiaSubgroupIn ℚ, ∀ v : (D₀.ρ.baseChangeAlong (x₀ : D₀.R →+* 𝒪) hx₀).V,
      (D₀.ρ.baseChangeAlong (x₀ : D₀.R →+* 𝒪) hx₀).ρ σ v - v ∈ L)
    (α : 𝒪)
    (hα : ∀ σ ∈ P.decompositionSubgroup ℚ, P.IsFrobeniusAt σ p →
      ∀ v : (D₀.ρ.baseChangeAlong (x₀ : D₀.R →+* 𝒪) hx₀).V,
        (D₀.ρ.baseChangeAlong (x₀ : D₀.R →+* 𝒪) hx₀).ρ σ v - α • v ∈ L)
    (Hdet : ∀ {A : Type} [CommRing A] [IsLocalRing A] [Algebra 𝒪 A] (ρA : GaloisRepAdic A),
      𝒟' ρA → ρA.DetIsCyclotomic p)
    (H1 : ∀ {A : Type} [CommRing A] [IsLocalRing A] [Algebra 𝒪 A] (ρA : GaloisRepAdic A)
        {B : Type} [CommRing B] [IsLocalRing B] [Algebra 𝒪 B] (f : A →+* B) (hf : IsLocalHom f),
      𝒟' ρA → 𝒟' (ρA.baseChangeAlong f hf))
    (Hord : ∀ {A : Type} [CommRing A] [IsLocalRing A] [Algebra 𝒪 A] (ρA : GaloisRepAdic A),
      𝒟' ρA → ρA.IsOrdinaryAt p)
    (H2 : ∀ {A : Type} [CommRing A] [IsLocalRing A] [Algebra 𝒪 A] (ρA : GaloisRepAdic A),
      𝒟' ρA → ρA.IsFlatAt p → 𝒟₀ ρA)
    (hα1 : α ^ 2 - 1 ≠ 0) (n : ℕ) :
    ∃ y : ((RingHom.ker (x₀.comp θ : D'.R →ₐ[𝒪] 𝒪)).Cotangent →ₗ[𝒪]
        𝒪 ⧸ (IsLocalRing.maximalIdeal 𝒪) ^ (n + 1)) →ₗ[𝒪] 𝒪 ⧸ (IsLocalRing.maximalIdeal 𝒪) ^ (n + 1),
      (∀ φ, (α ^ 2 - 1) • y φ = 0) ∧
      ∀ φ, y φ = 0 → φ ∈ LinearMap.ker (LinearMap.lcomp 𝒪 (𝒪 ⧸ (IsLocalRing.maximalIdeal 𝒪) ^ (n + 1))
        (LinearMap.ker (Ideal.mapCotangent (RingHom.ker (x₀.comp θ : D'.R →ₐ[𝒪] 𝒪))
            (RingHom.ker x₀) θ (fun _ hr => hr))).subtype) := by
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : NeZero p := ⟨hp.ne_zero⟩
  haveI hfin : Finite (IsLocalRing.ResidueField 𝒪) := hfl.1
  haveI hx' := isLocalHom_xPrime D₀ D' θ x₀ hx₀ hθ

  obtain ⟨k, hk⟩ : ∃ k : ℕ, α ^ 2 - 1 ∉ IsLocalRing.maximalIdeal 𝒪 ^ (k + 1) := by
    by_contra h
    simp only [not_exists, not_not] at h
    have : α ^ 2 - 1 ∈ ⨅ i : ℕ, IsLocalRing.maximalIdeal 𝒪 ^ i :=
      Ideal.mem_iInf.mpr fun i => Ideal.pow_le_pow_right (Nat.le_succ i) (h i)
    rw [Ideal.iInf_pow_eq_bot_of_isLocalRing _ (IsLocalRing.maximalIdeal.isMaximal 𝒪).ne_top] at this
    exact hα1 this
  set m : ℕ := n + 1 with hm
  set M : ℕ := m + k with hM
  have hmM : m ≤ M := Nat.le_add_right m k
  haveI : NeZero M := ⟨by omega⟩
  haveI : Finite (Rm 𝒪 m) := finite_Rm 𝒪 m
  haveI : Finite (Rm 𝒪 M) := finite_Rm 𝒪 M
  haveI : Finite (Am 𝒪 m) := finite_Am 𝒪 m

  obtain ⟨U, U', hU'U, hUU', hD, hI, hFr⟩ := PRungL2.Setup.exists_adapted_frame D₀ D' θ x₀ hx₀ hθ hθρ P L
    hLb hLD hLI {σ | ∃ h : σ ∈ P.decompositionSubgroup ℚ, P.IsFrobeniusAt σ p} α
    (fun σ hσ => hα σ hσ.1 hσ.2)

  have hdetP : (D'.ρ.baseChangeAlong (xPrime D₀ D' θ x₀ : D'.R →+* 𝒪) hx').DetIsCyclotomic p :=
    Hdet _ (H1 _ _ _ D'.isOfType)
  have hdetFad : ∀ (g : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (n a : ℕ),
      (∀ μ : AlgebraicClosure ℚ, μ ^ p ^ n = 1 → g μ = μ ^ a) →
        (Fad D₀ D' θ x₀ U U' g).det - (a : 𝒪) ∈ Ideal.span {((p ^ n : ℕ) : 𝒪)} :=
    fun g n a hμ => det_Fad_sub_mem_span D₀ D' θ x₀ hx₀ hθ U U' hUU' hdetP g n a hμ

  obtain ⟨g₀, hg₀, hg₀u⟩ := PRungL2.E4.exists_unitGap_inertia p hp hp2 hp𝔪 P hP (Fad D₀ D' θ x₀ U U') hI
    hdetFad (Rm 𝒪 m)
  replace hg₀u : IsUnit (Fadm D₀ D' θ x₀ U U' m g₀ 0 0 - Fadm D₀ D' θ x₀ U U' m g₀ 1 1) := hg₀u

  have hkey : ∀ φ : Φ' D₀ D' θ x₀ →ₗ[𝒪] Rm 𝒪 m,
      (∀ g ∈ P.decompositionSubgroup ℚ, Lam D₀ D' θ x₀ U U' m φ g 1 0 +
        w₁ D₀ D' θ x₀ U U' m g₀ φ * (Fadm D₀ D' θ x₀ U U' m g 1 1 - Fadm D₀ D' θ x₀ U U' m g 0 0) = 0) ∧
      (∀ τ ∈ P.inertiaSubgroupIn ℚ, Lam D₀ D' θ x₀ U U' m φ τ 1 1 -
        w₁ D₀ D' θ x₀ U U' m g₀ φ * Fadm D₀ D' θ x₀ U U' m τ 0 1 = 0) := by
    intro φ
    obtain ⟨cA, hcA⟩ := exists_basis_matrix_eq D₀ D' θ x₀ hx₀ hθ U U' m φ hUU'
    exact e3_keyFacts D₀ D' θ x₀ hx₀ hθ p P hP U U' hD hI m g₀ hg₀ hg₀u φ cA hcA
      (Hord _ (H1 _ _ _ D'.isOfType))
  have hF10 : ∀ (φ : Φ' D₀ D' θ x₀ →ₗ[𝒪] Rm 𝒪 m), ∀ g ∈ P.decompositionSubgroup ℚ,
      Ftil D₀ D' θ x₀ U U' m g₀ φ g 1 0 = 0 :=
    fun φ g hg => Ftil_10_eq_zero D₀ D' θ x₀ U U' m g₀ φ g (hD g hg) ((hkey φ).1 g hg)
  have hF11 : ∀ (φ : Φ' D₀ D' θ x₀ →ₗ[𝒪] Rm 𝒪 m), ∀ τ ∈ P.inertiaSubgroupIn ℚ,
      Ftil D₀ D' θ x₀ U U' m g₀ φ τ 1 1 = 1 :=
    fun φ τ hτ => Ftil_11_eq_one D₀ D' θ x₀ U U' m g₀ φ τ (hI τ hτ).2 ((hkey φ).2 τ hτ)
  have hFmul : ∀ (φ : Φ' D₀ D' θ x₀ →ₗ[𝒪] Rm 𝒪 m) (g h : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ),
      Ftil D₀ D' θ x₀ U U' m g₀ φ (g * h) = Ftil D₀ D' θ x₀ U U' m g₀ φ g * Ftil D₀ D' θ x₀ U U' m g₀ φ h :=
    fun φ g h => Ftil_mul D₀ D' θ x₀ U U' m g₀ φ hUU' (Mtil_mul D₀ D' θ x₀ m φ hx₀ hθ).1 g h
  have hFone : ∀ φ : Φ' D₀ D' θ x₀ →ₗ[𝒪] Rm 𝒪 m, Ftil D₀ D' θ x₀ U U' m g₀ φ 1 = 1 :=
    fun φ => Ftil_one D₀ D' θ x₀ U U' m g₀ φ hUU' (Mtil_mul D₀ D' θ x₀ m φ hx₀ hθ).2

  have hFdet : ∀ (φ : Φ' D₀ D' θ x₀ →ₗ[𝒪] Rm 𝒪 m) (g : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)
      (n a : ℕ), (∀ μ : AlgebraicClosure ℚ, μ ^ p ^ n = 1 → g μ = μ ^ a) →
        (Ftil D₀ D' θ x₀ U U' m g₀ φ g).det - (a : Am 𝒪 m) ∈ Ideal.span {((p ^ n : ℕ) : Am 𝒪 m)} := by
    intro φ g n a hμ
    exact det_Ftil_sub_mem_span D₀ D' θ x₀ hx₀ hθ U U' m g₀ φ hUU' (Hdet _ (H1 _ _ _ D'.isOfType)) g n a hμ

  have hlev := PRungL2.E3Disc.hlev_discharge D₀ D' θ x₀ hx₀ hθ U U' hU'U m M hmM g₀
    (fun φ => exists_basis_matrix_eq D₀ D' θ x₀ hx₀ hθ U U' m φ hUU')

  haveI : Module.Finite 𝒪 (Φ' D₀ D' θ x₀) := PRungL2.E3Univ.moduleFinite_cotangent (xPrime D₀ D' θ x₀)
  haveI : Finite (Φ' D₀ D' θ x₀ →ₗ[𝒪] Rm 𝒪 m) := PRungL2.E3Univ.finite_linearMap_of_moduleFinite
  obtain ⟨N, hMN, ζ, ϖ, hζ, hϖ, t, nn, u, βt, a, hu, huI, hβt, hdecφ, hdec0⟩ :=
    exists_universal_kummer_data D₀ D' θ x₀ hx₀ hθ p hp hp2 hp𝔪 P hP U U' hU'U hUU' hD hI hdetFad m M hmM
      g₀ hg₀ hg₀u hFmul hFone hF10 hF11 hFdet hlev
  have hpNm : ((p : ℕ) : Am 𝒪 m) ^ N = 0 := natCast_pow_eq_zero_Am_of_le 𝒪 m p hp𝔪 (hmM.trans hMN)
  have hpNM : ((p : ℕ) : Rm 𝒪 M) ^ N = 0 := natCast_pow_eq_zero_Rm_of_le 𝒪 M p hp𝔪 hMN
  have hϖ0 : ϖ ≠ 0 := by
    intro h; rw [h, zero_pow (pow_ne_zero _ hp.ne_zero)] at hϖ
    exact (Nat.cast_ne_zero.mpr hp.ne_zero) hϖ.symm

  have hβ : ∀ i, (ϖ ^ nn i * βt i) ^ p ^ N = (p : AlgebraicClosure ℚ) ^ (nn i) * u i := by
    intro i; rw [mul_pow, ← pow_mul, mul_comm (nn i), pow_mul, hϖ, hβt]

  obtain ⟨σ, hσ⟩ := ValuationSubring.exists_isFrobeniusAt_of_liesOverPrime_algebraicClosure_rat hp hP
  have hσD : σ ∈ P.decompositionSubgroup ℚ := hσ.mem_decompositionSubgroup
  obtain ⟨e, -, he⟩ : ∃ e < p ^ N, σ ζ = ζ ^ e := by
    have h1 : (σ ζ) ^ p ^ N = 1 := by rw [← map_pow, hζ.pow_eq_one, map_one]
    obtain ⟨e, he, he'⟩ := hζ.eq_pow_of_pow_eq_one h1
    exact ⟨e, he, he'.symm⟩

  set V : Rm 𝒪 M × ((Φ' D₀ D' θ x₀ →ₗ[𝒪] Rm 𝒪 m) →ₗ[𝒪] Rm 𝒪 m) := ∑ i, nn i • a i with hV

  have hsumφ : ∀ φ : Φ' D₀ D' θ x₀ →ₗ[𝒪] Rm 𝒪 m,
      ∑ i, nn i • evφ D₀ D' θ x₀ hmM φ (a i) = evφ D₀ D' θ x₀ hmM φ V := by
    intro φ; rw [hV, map_sum]; simp only [map_nsmul]
  have hsum0 : ∑ i, nn i • (a i).1 = V.1 := by
    rw [hV, Prod.fst_sum]
    exact Finset.sum_congr rfl fun i _ => rfl

  have hD_M : ∀ g ∈ P.decompositionSubgroup ℚ, Fadm D₀ D' θ x₀ U U' M g 1 0 = 0 := fun g hg => by
    rw [Fadm_apply, Fad, hD g hg, map_zero]
  have hI_M : ∀ τ ∈ P.inertiaSubgroupIn ℚ, Fadm D₀ D' θ x₀ U U' M τ 1 1 = 1 := fun τ hτ => by
    rw [Fadm_apply, Fad, (hI τ hτ).2, map_one]
  have hmulM := Fadm_mul D₀ D' θ x₀ U U' M hUU'
  have honeM := Fadm_one D₀ D' θ x₀ U U' M hU'U
  have hC5pt := ValuationSubring.sub_one_mul_sum_smul_eq_zero_of_corner_decomposition p hp hp2 N P hP ζ hζ
    (fun g => Fadm D₀ D' θ x₀ U U' M g 0 0) (fun g => Fadm D₀ D' θ x₀ U U' M g 1 1)
    (fun g => Fadm D₀ D' θ x₀ U U' M g 0 1)
    (PRungEntries.entry00_mul _ hmulM _ hD_M) (PRungEntries.entry11_mul _ hmulM _ hD_M)
    (PRungEntries.entry01_mul _ hmulM _)
    (PRungEntries.isUnit_entry00 _ hmulM honeM _ hD_M) (PRungEntries.isUnit_entry11 _ hmulM honeM _ hD_M) hI_M
    (fun g hg e' hg' => PRungEntries.entry00_mul_entry11_eq_of_det_eq _ _ hD_M g hg _
      (det_Fadm_eq_natCast D₀ D' θ x₀ U U' hdetFad M hpNM ζ hζ g e' hg'))
    nn u (fun i => ϖ ^ nn i * βt i) (fun i => (a i).1) hu huI hβ hdec0 σ hσD e he

  have hσ11 : Fad D₀ D' θ x₀ U U' σ 1 1 = α := (hFr σ ⟨hσD, hσ⟩).2
  beta_reduce at hC5pt
  rw [hsum0, Fadm_apply, hσ11, ← map_pow, ← map_one (algebraMap 𝒪 (Rm 𝒪 M)), ← map_sub] at hC5pt
  have hredV : red 𝒪 hmM V.1 = 0 := by
    obtain ⟨v, hv⟩ := Ideal.Quotient.mk_surjective V.1
    rw [← hv] at hC5pt ⊢
    rw [Ideal.Quotient.algebraMap_eq, ← map_mul, Ideal.Quotient.eq_zero_iff_mem] at hC5pt
    have hvm := IsDiscreteValuationRing.mem_maximalIdeal_pow_sub_of_mul_mem_of_not_mem (α ^ 2 - 1) v k M hk hC5pt
    rw [hM, Nat.add_sub_cancel] at hvm
    rw [red_mk, Ideal.Quotient.eq_zero_iff_mem]
    exact hvm
  have hfstV : ∀ φ : Φ' D₀ D' θ x₀ →ₗ[𝒪] Rm 𝒪 m, (evφ D₀ D' θ x₀ hmM φ V).fst = 0 := fun φ => by
    rw [fst_evφ, hredV]

  have hdetC5 : ∀ (φ : Φ' D₀ D' θ x₀ →ₗ[𝒪] Rm 𝒪 m), ∀ g ∈ P.decompositionSubgroup ℚ, ∀ e' : ℕ,
      g ζ = ζ ^ e' → Ftil D₀ D' θ x₀ U U' m g₀ φ g 0 0 * Ftil D₀ D' θ x₀ U U' m g₀ φ g 1 1 = e' := by
    intro φ g hg e' hg'
    refine PRungEntries.entry00_mul_entry11_eq_of_det_eq _ _ (hF10 φ) g hg _ ?_
    exact det_Ftil_eq_natCast D₀ D' θ x₀ hx₀ hθ U U' m g₀ φ hUU' (Hdet _ (H1 _ _ _ D'.isOfType)) hpNm ζ hζ
      g e' hg'
  refine ⟨V.2, fun φ => ?_, fun φ hφ => ?_⟩
  ·
    have hC5 := ValuationSubring.sub_one_mul_sum_smul_eq_zero_of_corner_decomposition p hp hp2 N P hP ζ hζ
      (fun g => Ftil D₀ D' θ x₀ U U' m g₀ φ g 0 0) (fun g => Ftil D₀ D' θ x₀ U U' m g₀ φ g 1 1)
      (fun g => Ftil D₀ D' θ x₀ U U' m g₀ φ g 0 1)
      (PRungEntries.entry00_mul _ (hFmul φ) _ (hF10 φ)) (PRungEntries.entry11_mul _ (hFmul φ) _ (hF10 φ))
      (PRungEntries.entry01_mul _ (hFmul φ) _)
      (PRungEntries.isUnit_entry00 _ (hFmul φ) (hFone φ) _ (hF10 φ))
      (PRungEntries.isUnit_entry11 _ (hFmul φ) (hFone φ) _ (hF10 φ)) (hF11 φ) (hdetC5 φ)
      nn u (fun i => ϖ ^ nn i * βt i) (fun i => evφ D₀ D' θ x₀ hmM φ (a i)) hu huI hβ (hdecφ φ) σ hσD e he
    beta_reduce at hC5
    rw [hsumφ] at hC5
    have hε := PRungTsze.snd_mul_eq_zero_of _ _ hC5 (hfstV φ)
    rw [fst_Ftil_apply, Fadm_apply, hσ11, snd_evφ] at hε
    show (α ^ 2 - 1) • V.2 φ = 0
    rw [Algebra.smul_def, map_sub, map_pow, map_one]
    exact hε
  ·
    have hV0 : evφ D₀ D' θ x₀ hmM φ V = 0 := by
      refine TrivSqZeroExt.ext ?_ ?_
      · rw [hfstV]; rfl
      · rw [snd_evφ]; exact hφ

    obtain ⟨bt, hbt⟩ := exists_basis_toMatrix_eq_Ftil D₀ D' θ x₀ hx₀ hθ U U' m g₀ φ hUU'
    obtain ⟨vLD, vLI, vcorner⟩ := vector_facts_of_basis D₀ D' θ x₀ hx₀ hθ U U' m g₀ φ P bt hbt (hF10 φ) (hF11 φ)

    have hdec' : ∀ τ ∈ P.inertiaSubgroupIn ℚ, (∀ ξ : AlgebraicClosure ℚ, ξ ^ p ^ N = 1 → τ ξ = ξ) →
        ∀ k' : Fin t → ℕ, (∀ i, τ (βt i) = ζ ^ (k' i) * βt i) →
          (D'.ρ.baseChangeAlong (xOfCotangentHom (xPrime D₀ D' θ x₀) φ : D'.R →+* Am 𝒪 m)
            (isLocalHom_xOfCotangentHom (xPrime D₀ D' θ x₀) φ)).ρ τ (bt 1) - bt 1 =
          (∑ i, (k' i) • evφ D₀ D' θ x₀ hmM φ (a i)) • bt 0 := by
      intro τ hτ hfix k' hk'
      have hpow : (τ ϖ * ϖ⁻¹) ^ p ^ N = 1 := by
        rw [mul_pow, ← map_pow, hϖ, map_natCast, inv_pow, hϖ,
          mul_inv_cancel₀ (Nat.cast_ne_zero.mpr hp.ne_zero)]
      obtain ⟨kϖ, -, hkϖ⟩ := hζ.eq_pow_of_pow_eq_one hpow
      have hkϖ' : τ ϖ = ζ ^ kϖ * ϖ := by
        rw [hkϖ, inv_mul_cancel_right₀ hϖ0]
      have hR := PRungL2.Reindex.corner_eq_kϖ_smul_add τ ζ ϖ hϖ0 nn (fun i => ϖ ^ nn i * βt i)
        (fun i => evφ D₀ D' θ x₀ hmM φ (a i)) (Ftil D₀ D' θ x₀ U U' m g₀ φ τ 0 1) (hdecφ φ τ hτ hfix) kϖ hkϖ'
        k' (fun i => by
          beta_reduce
          rw [mul_comm (ϖ ^ nn i) (βt i), mul_inv_cancel_right₀ (pow_ne_zero _ hϖ0)]
          exact hk' i)
      beta_reduce at hR
      rw [hsumφ, hV0, nsmul_zero, zero_add] at hR
      rw [vcorner τ hτ, hR]
    have hdetφ : (D'.ρ.baseChangeAlong (xOfCotangentHom (xPrime D₀ D' θ x₀) φ : D'.R →+* Am 𝒪 m)
        (isLocalHom_xOfCotangentHom (xPrime D₀ D' θ x₀) φ)).DetIsCyclotomic p :=
      Hdet _ (H1 D'.ρ (xOfCotangentHom (xPrime D₀ D' θ x₀) φ : D'.R →+* Am 𝒪 m)
        (isLocalHom_xOfCotangentHom (xPrime D₀ D' θ x₀) φ) D'.isOfType)
    have hflat := GaloisRepAdic.isFlatAt_of_ordinary_of_unitKummer_decomposition p hp2
      (D'.ρ.baseChangeAlong (xOfCotangentHom (xPrime D₀ D' θ x₀) φ : D'.R →+* Am 𝒪 m)
        (isLocalHom_xOfCotangentHom (xPrime D₀ D' θ x₀) φ))
      hdetφ P hP bt vLD vLI N hpNm ζ hζ u βt
      (fun i => evφ D₀ D' θ x₀ hmM φ (a i)) hu huI hβt hdec'
    exact mem_ker_lcomp_of_isOfType_dualNumberLift D₀ D' θ x₀ hθ hx₀ hθρ hθsurj H1 m φ
      (H2 _ (H1 D'.ρ (xOfCotangentHom (xPrime D₀ D' θ x₀) φ : D'.R →+* Am 𝒪 m)
        (isLocalHom_xOfCotangentHom (xPrime D₀ D' θ x₀) φ) D'.isOfType) hflat)

end PRungL2.Holes
p2m_reactivate "P2MW.S_GaloisRep_DeformationRingData_exists_localInvariant_of_ordinaryLine.PRungD P2MW.S_GaloisRep_DeformationRingData_exists_localInvariant_of_ordinaryLine.PRungInvDict"
p2m_reactivate "P2MW.S_GaloisRep_DeformationRingData_exists_localInvariant_of_ordinaryLine.PRungD P2MW.S_GaloisRep_DeformationRingData_exists_localInvariant_of_ordinaryLine.PRungInvDict"

theorem solution
    {𝒪 : Type} [CommRing 𝒪] [IsDomain 𝒪] [IsDiscreteValuationRing 𝒪]
    [IsAdicComplete (IsLocalRing.maximalIdeal 𝒪) 𝒪]
    {ρbar : ResidualGaloisRep (IsLocalRing.ResidueField 𝒪)}
    {𝒟₀ 𝒟' : ∀ ⦃A : Type⦄ [CommRing A] [IsLocalRing A] [Algebra 𝒪 A], GaloisRepAdic A → Prop}
    (D₀ : GaloisRep.DeformationRingData 𝒪 ρbar 𝒟₀) (D' : GaloisRep.DeformationRingData 𝒪 ρbar 𝒟')
    (θ : D'.R →ₐ[𝒪] D₀.R) (x₀ : D₀.R →ₐ[𝒪] 𝒪)
    (p : ℕ) (hp : p.Prime) (hp2 : p ≠ 2)
    (hp𝔪 : (p : 𝒪) ∈ IsLocalRing.maximalIdeal 𝒪)
    (hθ : IsLocalHom (θ : D'.R →+* D₀.R)) (hx₀ : IsLocalHom (x₀ : D₀.R →+* 𝒪))
    (hfl : (D₀.ρ.baseChangeAlong (x₀ : D₀.R →+* 𝒪) hx₀).IsFlatAt p)
    (hθρ : (D'.ρ.baseChangeAlong (θ : D'.R →+* D₀.R) hθ).IsEquiv D₀.ρ)
    (hθsurj : Function.Surjective θ)
    (P : ValuationSubring (AlgebraicClosure ℚ)) (hP : P.LiesOverPrime p)
    (L : Submodule 𝒪 (D₀.ρ.baseChangeAlong (x₀ : D₀.R →+* 𝒪) hx₀).V)
    (hLb : ∃ b : Module.Basis (Fin 2) 𝒪 (D₀.ρ.baseChangeAlong (x₀ : D₀.R →+* 𝒪) hx₀).V, L = 𝒪 ∙ b 0)
    (hLD : ∀ σ ∈ P.decompositionSubgroup ℚ, ∀ v ∈ L,
      (D₀.ρ.baseChangeAlong (x₀ : D₀.R →+* 𝒪) hx₀).ρ σ v ∈ L)
    (hLI : ∀ σ ∈ P.inertiaSubgroupIn ℚ, ∀ v : (D₀.ρ.baseChangeAlong (x₀ : D₀.R →+* 𝒪) hx₀).V,
      (D₀.ρ.baseChangeAlong (x₀ : D₀.R →+* 𝒪) hx₀).ρ σ v - v ∈ L)
    (α : 𝒪)
    (hα : ∀ σ ∈ P.decompositionSubgroup ℚ, P.IsFrobeniusAt σ p →
      ∀ v : (D₀.ρ.baseChangeAlong (x₀ : D₀.R →+* 𝒪) hx₀).V,
        (D₀.ρ.baseChangeAlong (x₀ : D₀.R →+* 𝒪) hx₀).ρ σ v - α • v ∈ L)
    (Hdet : ∀ {A : Type} [CommRing A] [IsLocalRing A] [Algebra 𝒪 A] (ρA : GaloisRepAdic A),
      𝒟' ρA → ρA.DetIsCyclotomic p)
    (H1 : ∀ {A : Type} [CommRing A] [IsLocalRing A] [Algebra 𝒪 A] (ρA : GaloisRepAdic A)
        {B : Type} [CommRing B] [IsLocalRing B] [Algebra 𝒪 B] (f : A →+* B) (hf : IsLocalHom f),
      𝒟' ρA → 𝒟' (ρA.baseChangeAlong f hf))
    (Hord : ∀ {A : Type} [CommRing A] [IsLocalRing A] [Algebra 𝒪 A] (ρA : GaloisRepAdic A),
      𝒟' ρA → ρA.IsOrdinaryAt p)
    (H2 : ∀ {A : Type} [CommRing A] [IsLocalRing A] [Algebra 𝒪 A] (ρA : GaloisRepAdic A),
      𝒟' ρA → ρA.IsFlatAt p → 𝒟₀ ρA)
    (hα1 : α ^ 2 - 1 ≠ 0) (n : ℕ) :
    ∃ y : ((RingHom.ker (x₀.comp θ : D'.R →ₐ[𝒪] 𝒪)).Cotangent →ₗ[𝒪]
        𝒪 ⧸ (IsLocalRing.maximalIdeal 𝒪) ^ (n + 1)) →ₗ[𝒪] 𝒪 ⧸ (IsLocalRing.maximalIdeal 𝒪) ^ (n + 1),
      (∀ φ, (α ^ 2 - 1) • y φ = 0) ∧
      ∀ φ, y φ = 0 → φ ∈ LinearMap.ker (LinearMap.lcomp 𝒪 (𝒪 ⧸ (IsLocalRing.maximalIdeal 𝒪) ^ (n + 1))
        (LinearMap.ker (Ideal.mapCotangent (RingHom.ker (x₀.comp θ : D'.R →ₐ[𝒪] 𝒪))
            (RingHom.ker x₀) θ (fun _ hr => hr))).subtype) := by
  exact PRungL2.Holes.exists_local_invariant D₀ D' θ x₀ p hp hp2 hp𝔪 hθ hx₀ hfl hθρ hθsurj P hP L hLb hLD hLI α hα
    Hdet H1 Hord H2 hα1 n

end S_GaloisRep_DeformationRingData_exists_localInvariant_of_ordinaryLine
end P2MW
export P2MW.S_GaloisRep_DeformationRingData_exists_localInvariant_of_ordinaryLine (solution)
