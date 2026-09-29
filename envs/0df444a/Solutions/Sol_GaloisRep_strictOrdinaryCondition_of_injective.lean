-- Prove2me | solution 1 for GaloisRep.strictOrdinaryCondition_of_injective
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:07.331093+00:00
-- url     : https://prove2.me/submissions/c39dac58-f358-58ec-9326-486e93b396be

import Mathlib
import Definitions.Def_GaloisRep_StrictOrdinary
import Theorems.Thm_GaloisRep_ordinaryCondition_of_injective
import Theorems.Thm_GaloisRepAdic_ordinaryLine_eq_of_exists_inertia_residual_ne_one
import Theorems.Thm_GaloisRepAdic_exists_mem_inertiaSubgroupIn_residual_ne_one_of_detIsCyclotomic
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_GaloisRep_strictOrdinaryCondition_of_injective

set_option autoImplicit false

namespace GaloisRep
p2m_export "GaloisRep" "strictOrdinaryCondition ordinaryCondition_of_strictOrdinaryCondition ordinaryCondition_of_injective"
namespace S2StrictReflectAux
p2m_open "GaloisRep"

open TensorProduct

theorem mem_span_iff_repr_one_eq_zero {R V : Type} [CommRing R] [AddCommGroup V] [Module R V]
    (b : Module.Basis (Fin 2) R V) (v : V) : v ∈ R ∙ b 0 ↔ b.repr v 1 = 0 := by
  constructor
  · intro hv
    obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hv
    simp
  · intro hv
    have := b.sum_repr v
    rw [Fin.sum_univ_two, hv, zero_smul, add_zero] at this
    rw [← this]
    exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self _)

theorem forall_sub_smul_mem_span_iff {R V : Type} [CommRing R] [AddCommGroup V] [Module R V]
    (b : Module.Basis (Fin 2) R V) (M : Module.End R V) (z : R) :
    (∀ v, M v - z • v ∈ R ∙ b 0) ↔ b.repr (M (b 0)) 1 = 0 ∧ b.repr (M (b 1)) 1 = z := by
  simp_rw [mem_span_iff_repr_one_eq_zero b]
  constructor
  · intro h
    have h0 := h (b 0)
    have h1 := h (b 1)
    simp at h0 h1
    exact ⟨h0, sub_eq_zero.mp h1⟩
  · rintro ⟨h0, h1⟩ v
    have key :
        (Finsupp.lapply (1 : Fin 2) ∘ₗ b.repr.toLinearMap) ∘ₗ (M - z • LinearMap.id) = 0 := by
      apply b.ext
      refine Fin.forall_fin_two.mpr ⟨?_, ?_⟩
      · simp [h0]
      · simp [h1]
    have := LinearMap.congr_fun key v
    simpa using this

theorem basis_repr_baseChange_apply {A B V : Type} [CommRing A] [CommRing B] [Algebra A B]
    [AddCommGroup V] [Module A V] (b : Module.Basis (Fin 2) A V) (M : Module.End A V)
    (i j : Fin 2) :
    (Algebra.TensorProduct.basis B b).repr
        (M.baseChange B (Algebra.TensorProduct.basis B b j)) i =
      algebraMap A B (b.repr (M (b j)) i) := by
  rw [Algebra.TensorProduct.basis_apply, LinearMap.baseChange_tmul,
    Algebra.TensorProduct.basis_repr_tmul]
  simp

theorem forall_baseChange_sub_smul_mem_span {A B V : Type} [CommRing A] [CommRing B] [Algebra A B]
    [AddCommGroup V] [Module A V] (b : Module.Basis (Fin 2) A V) (M : Module.End A V) (z : A)
    (h : ∀ v, M v - z • v ∈ A ∙ b 0) :
    ∀ v, M.baseChange B v - algebraMap A B z • v ∈ B ∙ Algebra.TensorProduct.basis B b 0 := by
  rw [forall_sub_smul_mem_span_iff] at h ⊢
  rw [basis_repr_baseChange_apply, basis_repr_baseChange_apply, h.1, h.2, map_zero]
  exact ⟨rfl, rfl⟩

theorem forall_mem_span_apply_eq_repr_smul {R V : Type} [CommRing R] [AddCommGroup V] [Module R V]
    (b : Module.Basis (Fin 2) R V) (M : Module.End R V) (hL : M (b 0) ∈ R ∙ b 0) :
    ∀ w ∈ R ∙ b 0, M w = (b.repr (M (b 0)) 0) • w := by
  obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp hL
  have hx : b.repr (M (b 0)) 0 = c := by rw [← hc]; simp
  intro w hw
  obtain ⟨d, rfl⟩ := Submodule.mem_span_singleton.mp hw
  rw [hx, map_smul, ← hc, smul_comm]

theorem eq_repr_of_forall_mem_span_apply_eq_smul {R V : Type} [CommRing R] [AddCommGroup V]
    [Module R V] (b : Module.Basis (Fin 2) R V) (M : Module.End R V) (x : R)
    (hx : ∀ w ∈ R ∙ b 0, M w = x • w) : x = b.repr (M (b 0)) 0 := by
  have := congrArg (fun v => b.repr v 0) (hx (b 0) (Submodule.mem_span_singleton_self _))
  simp at this
  exact this.symm

theorem exists_nat_forall_pow_eq_one_apply_eq_pow {F L : Type} [Field F] [Field L] [Algebra F L]
    (σ : L ≃ₐ[F] L) (n : ℕ) [NeZero n] :
    ∃ m : ℕ, ∀ μ : L, μ ^ n = 1 → σ μ = μ ^ m := by
  obtain ⟨m, hm⟩ := rootsOfUnity.integer_power_of_ringEquiv' n (σ : L ≃+* L)
  refine ⟨(m % (n : ℤ)).toNat, fun μ hμ => ?_⟩
  have ht := hm (rootsOfUnity.mkOfPowEq μ hμ : Lˣ) (rootsOfUnity.mkOfPowEq μ hμ).2
  rw [rootsOfUnity.val_mkOfPowEq_coe, AlgEquiv.coe_ringEquiv] at ht
  rw [ht]
  have hn : ((rootsOfUnity.mkOfPowEq μ hμ : Lˣ)) ^ n = 1 := (rootsOfUnity.mkOfPowEq μ hμ).2
  rw [zpow_eq_zpow_emod' m hn]
  have h0 : (0 : ℤ) ≤ m % (n : ℤ) := Int.emod_nonneg _ (by exact_mod_cast (NeZero.ne n))
  conv_lhs => rw [← Int.toNat_of_nonneg h0, zpow_natCast]
  rw [Units.val_pow_eq_pow_val, rootsOfUnity.val_mkOfPowEq_coe]

end GaloisRep.S2StrictReflectAux

theorem solution
    {A B : Type} [CommRing A] [IsLocalRing A] [CommRing B] [IsLocalRing B]
    (𝒪 : Type) [CommRing 𝒪] [Algebra 𝒪 A] [Algebra 𝒪 B]
    (φ : A →+* B) (hφ : IsLocalHom φ) (hinj : Function.Injective φ) (ρ : GaloisRepAdic A)
    {p : ℕ} {S : Finset ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hnB : IsNilpotent (p : B))
    (h : GaloisRep.strictOrdinaryCondition 𝒪 p S (ρ.baseChangeAlong φ hφ)) :
    GaloisRep.strictOrdinaryCondition 𝒪 p S ρ := by
  classical

  obtain ⟨hdetA, hordA, hunrA⟩ := GaloisRep.ordinaryCondition_of_injective 𝒪 φ hφ hinj ρ hp hp2 hnB
    (GaloisRep.ordinaryCondition_of_strictOrdinaryCondition h)
  obtain ⟨hdetB, hstrB, -⟩ := h
  refine ⟨hdetA, ⟨hdetA.1, fun P hP => ?_⟩, hunrA⟩
  obtain ⟨L, ⟨b, rfl⟩, hD, hI⟩ := hordA P hP
  refine ⟨A ∙ b 0, ⟨b, rfl⟩, hD, hI, fun σ hσ => ?_⟩

  have h00 : ρ.ρ σ (b 0) ∈ A ∙ b 0 := hD σ hσ _ (Submodule.mem_span_singleton_self _)
  refine ⟨b.repr (ρ.ρ σ (b 0)) 0, b.repr (ρ.ρ σ (b 1)) 1,
    GaloisRep.S2StrictReflectAux.forall_mem_span_apply_eq_repr_smul b _ h00,
    (GaloisRep.S2StrictReflectAux.forall_sub_smul_mem_span_iff b _ _).mpr
      ⟨(GaloisRep.S2StrictReflectAux.mem_span_iff_repr_one_eq_zero b _).mp h00, rfl⟩,
    fun n a hμ => ?_⟩

  letI : Algebra A B := φ.toAlgebra
  haveI : NeZero p := ⟨hp.ne_zero⟩
  let bB : Module.Basis (Fin 2) B (ρ.baseChangeAlong φ hφ).V := Algebra.TensorProduct.basis B b
  have hIB : ∀ τ ∈ P.inertiaSubgroupIn ℚ, ∀ v : (ρ.baseChangeAlong φ hφ).V,
      (ρ.baseChangeAlong φ hφ).ρ τ v - v ∈ (B ∙ bB 0 : Submodule B (ρ.baseChangeAlong φ hφ).V) := by
    intro τ hτ v
    have h1 : ∀ w : ρ.V, ρ.ρ τ w - (1 : A) • w ∈ A ∙ b 0 := fun w => by
      rw [one_smul]; exact hI τ hτ w
    have := GaloisRep.S2StrictReflectAux.forall_baseChange_sub_smul_mem_span
      (B := B) b (ρ.ρ τ) 1 h1 v
    rw [map_one, one_smul] at this
    exact this

  obtain ⟨L', hL'b, hD', hI', hS'⟩ := hstrB.2 P hP
  obtain ⟨τ, hτ, hne⟩ :=
    GaloisRepAdic.exists_mem_inertiaSubgroupIn_residual_ne_one_of_detIsCyclotomic
      (ρ.baseChangeAlong φ hφ) hp hp2 hdetB P hP
  have hLL' : (B ∙ bB 0 : Submodule B (ρ.baseChangeAlong φ hφ).V) = L' :=
    GaloisRepAdic.ordinaryLine_eq_of_exists_inertia_residual_ne_one (ρ.baseChangeAlong φ hφ) P _ L'
      ⟨bB, rfl⟩ hL'b hIB hI' ⟨τ, hτ, hne⟩
  subst hLL'
  obtain ⟨x', z', hx', hz', hcong⟩ := hS' σ hσ

  have hx'e : x' = φ (b.repr (ρ.ρ σ (b 0)) 0) := by
    rw [GaloisRep.S2StrictReflectAux.eq_repr_of_forall_mem_span_apply_eq_smul bB _ x' hx']
    have e := GaloisRep.S2StrictReflectAux.basis_repr_baseChange_apply (B := B) b (ρ.ρ σ) 0 0
    rw [RingHom.algebraMap_toAlgebra] at e
    exact e
  have hz'e : z' = φ (b.repr (ρ.ρ σ (b 1)) 1) := by
    rw [← ((GaloisRep.S2StrictReflectAux.forall_sub_smul_mem_span_iff bB _ z').mp hz').2]
    have e := GaloisRep.S2StrictReflectAux.basis_repr_baseChange_apply (B := B) b (ρ.ρ σ) 1 1
    rw [RingHom.algebraMap_toAlgebra] at e
    exact e

  obtain ⟨N, hN⟩ := hnB
  obtain ⟨a', ha'⟩ :=
    GaloisRep.S2StrictReflectAux.exists_nat_forall_pow_eq_one_apply_eq_pow σ (p ^ (n + N))
  have htop := hcong (n + N) a' ha'
  have hpB : ((p ^ (n + N) : ℕ) : B) = 0 := by rw [Nat.cast_pow, pow_add, hN, mul_zero]
  rw [hpB, Ideal.mem_span_singleton, zero_dvd_iff, sub_eq_zero, hx'e, hz'e] at htop

  have hxaz : b.repr (ρ.ρ σ (b 0)) 0 - (a' : A) * b.repr (ρ.ρ σ (b 1)) 1 = 0 := by
    apply hinj
    rw [map_sub, map_mul, map_natCast, htop, sub_self, map_zero]

  obtain ⟨ζ, hζ⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot (AlgebraicClosure ℚ) (p ^ n)
  have hζ1 : σ ζ = ζ ^ a := hμ ζ hζ.pow_eq_one
  have hζ2 : σ ζ = ζ ^ a' := ha' ζ (by rw [pow_add, pow_mul, hζ.pow_eq_one, one_pow])
  have hζu : IsUnit ζ := hζ.isUnit (NeZero.ne (p ^ n))
  have hu : IsPrimitiveRoot hζu.unit (p ^ n) :=
    IsPrimitiveRoot.coe_units_iff.mp (by rw [hζu.unit_spec]; exact hζ)
  have hpow : hζu.unit ^ a = hζu.unit ^ a' := by
    ext
    rw [Units.val_pow_eq_pow_val, Units.val_pow_eq_pow_val, hζu.unit_spec]
    exact hζ1.symm.trans hζ2
  have hmod : a ≡ a' [MOD p ^ n] := by
    rw [hu.eq_orderOf]; exact pow_eq_pow_iff_modEq.mp hpow
  obtain ⟨c, hc⟩ := Nat.modEq_iff_dvd.mp hmod
  have hc' : ((a' : ℕ) : A) - ((a : ℕ) : A) = (p : A) ^ n * (c : A) := by
    have := congrArg (Int.cast : ℤ → A) hc
    push_cast at this
    exact this
  refine Ideal.mem_span_singleton'.mpr ⟨(c : A) * b.repr (ρ.ρ σ (b 1)) 1, ?_⟩
  rw [Nat.cast_pow]
  linear_combination (-1 : A) * hxaz + (-(b.repr (ρ.ρ σ (b 1)) 1)) * hc'

end S_GaloisRep_strictOrdinaryCondition_of_injective
end P2MW
export P2MW.S_GaloisRep_strictOrdinaryCondition_of_injective (solution)
