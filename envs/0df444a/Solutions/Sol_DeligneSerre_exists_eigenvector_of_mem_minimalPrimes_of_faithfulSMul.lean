-- Prove2me | solution 1 for DeligneSerre.exists_eigenvector_of_mem_minimalPrimes_of_faithfulSMul
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.805612+00:00
-- url     : https://prove2.me/submissions/90432ae7-cc33-5eaf-b977-c3057caabb7e

import Mathlib.RingTheory.Ideal.AssociatedPrime.Localization
import Mathlib.RingTheory.Artinian.Module
import Mathlib.RingTheory.HopkinsLevitzki
import Mathlib.RingTheory.Ideal.MinimalPrime.Noetherian
import Mathlib.FieldTheory.IsAlgClosed.Basic
import Mathlib.Algebra.Algebra.Subalgebra.Lattice
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_DeligneSerre_exists_eigenvector_of_mem_minimalPrimes_of_faithfulSMul

set_option autoImplicit false

namespace DeligneSerre

open Module

open scoped IsMulCommutative in

theorem exists_eigenvector_of_mem_minimalPrimes_of_faithfulSMul_impl
    {K : Type*} [Field K] [IsAlgClosed K]
    {V : Type*} [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    {T : Type*} [CommRing T] [Module T V] [SMulCommClass T K V] [FaithfulSMul T V]
    {𝔭 : Ideal T} (h𝔭 : 𝔭 ∈ minimalPrimes T) :
    ∃ χ : T →+* K, RingHom.ker χ = 𝔭 ∧
      ∃ x : V, x ≠ 0 ∧ (∀ p ∈ 𝔭, p • x = 0) ∧ (∀ r : T, r • x = 0 → r ∈ 𝔭) ∧
        ∀ t : T, t • x = χ t • x := by
  classical

  let φ : T →+* Module.End K V := Module.toModuleEnd K V
  have hφ : ∀ (t : T) (v : V), φ t v = t • v := fun t v => rfl
  have hφinj : Function.Injective φ := by
    intro t t' h
    exact FaithfulSMul.eq_of_smul_eq_smul (M := T) (α := V) fun v => by
      rw [← hφ, ← hφ, h]

  let A : Subalgebra K (Module.End K V) := Algebra.adjoin K (Set.range φ)
  haveI : IsMulCommutative A := Algebra.isMulCommutative_adjoin (R := K) (by
    rintro _ ⟨t, rfl⟩ _ ⟨t', rfl⟩
    rw [← map_mul, ← map_mul, mul_comm])
  haveI : Module.Finite K A := Module.Finite.of_injective A.val.toLinearMap Subtype.val_injective
  haveI : IsArtinianRing A := IsArtinianRing.of_finite K A

  haveI : IsScalarTower K A V := ⟨fun c a v => by
    simp only [Subalgebra.smul_def, Subalgebra.coe_smul, LinearMap.smul_apply,
      Module.End.smul_def]⟩
  haveI : Module.Finite A V := Module.Finite.of_restrictScalars_finite K A V
  have hann : Module.annihilator A V = ⊥ := by
    rw [eq_bot_iff]
    intro a ha
    rw [Module.mem_annihilator] at ha
    rw [Submodule.mem_bot]
    exact Subtype.ext (LinearMap.ext fun v => by simpa [Subalgebra.smul_def] using ha v)

  let φA : T →+* A := φ.codRestrict A fun t => Algebra.subset_adjoin ⟨t, rfl⟩
  have hφA : ∀ t : T, ((φA t : A) : Module.End K V) = φ t := fun t => rfl
  have hφAinj : Function.Injective φA := fun t t' h =>
    hφinj (by rw [← hφA, ← hφA, h])
  have hφAsmul : ∀ (t : T) (v : V), φA t • v = t • v := fun t v => rfl

  haveI h𝔭prime : 𝔭.IsPrime := h𝔭.1.1
  have hfin : (minimalPrimes A).Finite := minimalPrimes.finite_of_isNoetherianRing A
  obtain ⟨𝔓, h𝔓min, h𝔓le⟩ : ∃ 𝔓 ∈ minimalPrimes A, 𝔓.comap φA ≤ 𝔭 := by
    have hinf : hfin.toFinset.inf (fun 𝔓 => 𝔓.comap φA) ≤ 𝔭 := by
      intro t ht
      have hmem : φA t ∈ sInf (minimalPrimes A) := by
        rw [Ideal.mem_sInf]
        intro 𝔓 h𝔓
        have hle : hfin.toFinset.inf (fun 𝔓 => 𝔓.comap φA) ≤ 𝔓.comap φA :=
          Finset.inf_le (hfin.mem_toFinset.mpr h𝔓)
        exact Ideal.mem_comap.mp (hle ht)
      have hnil : IsNilpotent (φA t) := by
        have h' : φA t ∈ (⊥ : Ideal A).radical := by
          rw [← Ideal.sInf_minimalPrimes]; exact hmem
        exact h'
      obtain ⟨n, hn⟩ := hnil
      have htn : t ^ n = 0 := hφAinj (by rw [map_pow, hn, map_zero])
      exact h𝔭prime.mem_of_pow_mem n (htn ▸ 𝔭.zero_mem)
    obtain ⟨𝔓, h𝔓S, h𝔓le⟩ := (Ideal.IsPrime.inf_le' h𝔭prime).mp hinf
    exact ⟨𝔓, hfin.mem_toFinset.mp h𝔓S, h𝔓le⟩
  haveI h𝔓prime : 𝔓.IsPrime := h𝔓min.1.1
  have hcomap : 𝔓.comap φA = 𝔭 :=
    le_antisymm h𝔓le (h𝔭.2 ⟨Ideal.comap_isPrime φA 𝔓, bot_le⟩ h𝔓le)

  have hass : 𝔓 ∈ associatedPrimes A V := by
    refine Module.associatedPrimes.minimalPrimes_annihilator_subset_associatedPrimes A V ?_
    rw [hann]
    exact h𝔓min
  obtain ⟨-, x, hx⟩ := (isAssociatedPrime_iff.mp hass)
  have hx' : ∀ a : A, a ∈ 𝔓 ↔ a • x = 0 := fun a => by
    rw [hx, Submodule.mem_colon_singleton, Submodule.mem_bot]
  have hx0 : x ≠ 0 := by
    intro h0
    apply h𝔓prime.ne_top
    rw [eq_top_iff]
    intro a _
    rw [hx' a, h0, smul_zero]

  haveI : 𝔓.IsMaximal := IsArtinianRing.isMaximal_of_isPrime 𝔓
  haveI : Module.Finite K (A ⧸ 𝔓) :=
    Module.Finite.of_surjective (Ideal.Quotient.mkₐ K 𝔓).toLinearMap
      (Ideal.Quotient.mkₐ_surjective K 𝔓)
  haveI : Algebra.IsIntegral K (A ⧸ 𝔓) := Algebra.IsIntegral.of_finite K _
  let e : K ≃+* A ⧸ 𝔓 :=
    RingEquiv.ofBijective (algebraMap K (A ⧸ 𝔓)) IsAlgClosed.algebraMap_bijective_of_isIntegral
  let χA : A →+* K := e.symm.toRingHom.comp (Ideal.Quotient.mk 𝔓)
  have hχA : ∀ a : A, a - algebraMap K A (χA a) ∈ 𝔓 := by
    intro a
    rw [← Ideal.Quotient.eq_zero_iff_mem, map_sub, sub_eq_zero, Ideal.Quotient.mk_algebraMap]
    change Ideal.Quotient.mk 𝔓 a = e (e.symm (Ideal.Quotient.mk 𝔓 a))
    exact (e.apply_symm_apply (Ideal.Quotient.mk 𝔓 a)).symm
  have hkerA : RingHom.ker χA = 𝔓 := by
    ext a
    rw [RingHom.mem_ker]
    change e.symm (Ideal.Quotient.mk 𝔓 a) = 0 ↔ a ∈ 𝔓
    rw [EmbeddingLike.map_eq_zero_iff, Ideal.Quotient.eq_zero_iff_mem]
  have heigA : ∀ a : A, a • x = χA a • x := by
    intro a
    have h := (hx' _).mp (hχA a)
    rwa [sub_smul, sub_eq_zero, algebraMap_smul] at h

  refine ⟨χA.comp φA, ?_, x, hx0, ?_, ?_, ?_⟩
  · rw [← RingHom.comap_ker, hkerA, hcomap]
  · intro p hp
    have : φA p ∈ 𝔓 := by rw [← hcomap] at hp; exact Ideal.mem_comap.mp hp
    rw [← hφAsmul, (hx' _).mp this]
  · intro r hr
    rw [← hcomap, Ideal.mem_comap, hx', hφAsmul]
    exact hr
  · intro t
    rw [← hφAsmul, heigA]
    rfl

end DeligneSerre

theorem solution
    {K : Type*} [Field K] [IsAlgClosed K]
    {V : Type*} [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    {T : Type*} [CommRing T] [Module T V] [SMulCommClass T K V] [FaithfulSMul T V]
    {𝔭 : Ideal T} (h𝔭 : 𝔭 ∈ minimalPrimes T) :
    ∃ χ : T →+* K, RingHom.ker χ = 𝔭 ∧
      ∃ x : V, x ≠ 0 ∧ (∀ p ∈ 𝔭, p • x = 0) ∧ (∀ r : T, r • x = 0 → r ∈ 𝔭) ∧
        ∀ t : T, t • x = χ t • x :=
  DeligneSerre.exists_eigenvector_of_mem_minimalPrimes_of_faithfulSMul_impl (h𝔭 := h𝔭)

#print axioms solution

end S_DeligneSerre_exists_eigenvector_of_mem_minimalPrimes_of_faithfulSMul
end P2MW
export P2MW.S_DeligneSerre_exists_eigenvector_of_mem_minimalPrimes_of_faithfulSMul (solution)
