-- Prove2me | solution 1 for GaloisRepAdic.exists_pow_prime_pow_eq_one_of_wild
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.805612+00:00
-- url     : https://prove2.me/submissions/fc6f79a9-285d-5919-8dd4-02ed28a4e416

import Definitions.Def_GaloisRep_Adic
import Theorems.Thm_ValuationSubring_exists_forall_pow_prime_pow_apply_eq_self_of_wild
import Mathlib.RingTheory.Filtration
import Mathlib.FieldTheory.Normal.Closure
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_GaloisRepAdic_exists_pow_prime_pow_eq_one_of_wild

set_option autoImplicit false
open Polynomial

namespace WildOrder

section Small

variable {A V : Type} [CommRing A] [AddCommGroup V] [Module A V]

def Small (I : Ideal A) (n : ℕ) (D : Module.End A V) : Prop :=
  ∀ v : V, D v ∈ (I ^ n • ⊤ : Submodule A V)

variable {I : Ideal A}

theorem Small.mono {m n : ℕ} (h : m ≤ n) {D : Module.End A V} (hD : Small I n D) : Small I m D :=
  fun v => Submodule.smul_mono_left (Ideal.pow_le_pow_right h) (hD v)

theorem Small.zero (n : ℕ) : Small I n (0 : Module.End A V) :=
  fun v => by rw [LinearMap.zero_apply]; exact Submodule.zero_mem _

theorem Small.add {n : ℕ} {D D' : Module.End A V} (hD : Small I n D) (hD' : Small I n D') :
    Small I n (D + D') :=
  fun v => by rw [LinearMap.add_apply]; exact Submodule.add_mem _ (hD v) (hD' v)

theorem Small.sub {n : ℕ} {D D' : Module.End A V} (hD : Small I n D) (hD' : Small I n D') :
    Small I n (D - D') :=
  fun v => by rw [LinearMap.sub_apply]; exact Submodule.sub_mem _ (hD v) (hD' v)

theorem Small.nsmul {n : ℕ} {D : Module.End A V} (hD : Small I n D) (N : ℕ) : Small I n (N • D) :=
  fun v => by rw [LinearMap.smul_apply]; exact nsmul_mem (hD v) N

theorem Small.mul_right {n : ℕ} {D : Module.End A V} (hD : Small I n D) (D' : Module.End A V) :
    Small I n (D * D') :=
  fun v => by rw [Module.End.mul_apply]; exact hD (D' v)

theorem Small.mul {m n : ℕ} {D D' : Module.End A V} (hD : Small I n D) (hD' : Small I m D') :
    Small I (m + n) (D * D') := by
  intro v
  rw [Module.End.mul_apply]
  have h1 : D (D' v) ∈ (I ^ m • ⊤ : Submodule A V).map D := Submodule.mem_map_of_mem (hD' v)
  rw [Submodule.map_smul''] at h1
  have h2 : (⊤ : Submodule A V).map D ≤ I ^ n • ⊤ := by
    rintro w ⟨u, -, rfl⟩
    exact hD u
  have h3 : I ^ m • (⊤ : Submodule A V).map D ≤ I ^ (m + n) • ⊤ :=
    calc I ^ m • (⊤ : Submodule A V).map D ≤ I ^ m • (I ^ n • ⊤) := Submodule.smul_mono le_rfl h2
      _ = I ^ (m + n) • ⊤ := by rw [← Submodule.mul_smul, ← pow_add]
  exact h3 h1

theorem Small.one_add_pow_sub_one {n : ℕ} {D : Module.End A V} (hD : Small I n D) (N : ℕ) :
    Small I n ((1 + D) ^ N - 1) := by
  induction N with
  | zero =>
      rw [pow_zero, sub_self]
      exact Small.zero n
  | succ N ih =>
      have e : (1 + D) ^ (N + 1) - 1 = ((1 + D) ^ N - 1) + ((1 + D) ^ N - 1) * D + D := by
        rw [pow_succ, mul_add, mul_one, sub_mul, one_mul]
        abel
      rw [e]
      exact (ih.add (ih.mul_right D)).add hD

theorem Small.one_add_pow_sub_one_sub_nsmul {n : ℕ} {D : Module.End A V} (hD : Small I n D) (N : ℕ) :
    Small I (n + n) ((1 + D) ^ N - 1 - N • D) := by
  induction N with
  | zero =>
      rw [pow_zero, sub_self, zero_smul, sub_zero]
      exact Small.zero _
  | succ N ih =>
      have e : (1 + D) ^ (N + 1) - 1 - (N + 1) • D
          = ((1 + D) ^ N - 1 - N • D) + ((1 + D) ^ N - 1 - N • D) * D + N • (D * D) := by
        rw [pow_succ, mul_add, mul_one, succ_nsmul, sub_mul, sub_mul, one_mul, smul_mul_assoc]
        abel
      rw [e]
      exact (ih.add (ih.mul_right D)).add ((hD.mul hD).nsmul N)

end Small

theorem isUnit_natCast_of_prime_ne {A : Type} [CommRing A] [IsLocalRing A] {p q : ℕ} (hp : p.Prime)
    (hq : q.Prime) (hqp : q ≠ p) (hpA : (p : A) ∈ IsLocalRing.maximalIdeal A) : IsUnit (q : A) := by
  have hcop : IsCoprime (p : ℤ) (q : ℤ) :=
    Nat.isCoprime_iff_coprime.mpr ((Nat.coprime_primes hp hq).mpr hqp.symm)
  have hA : IsCoprime (p : A) (q : A) := by simpa using hcop.map (Int.castRingHom A)
  by_contra hqu
  have hqm : (q : A) ∈ IsLocalRing.maximalIdeal A := by
    by_contra h
    exact hqu (IsLocalRing.notMem_maximalIdeal.mp h)
  obtain ⟨u, v, huv⟩ := hA
  have h1 : (1 : A) ∈ IsLocalRing.maximalIdeal A := by
    rw [← huv]
    exact Ideal.add_mem _ (Ideal.mul_mem_left _ _ hpA) (Ideal.mul_mem_left _ _ hqm)
  exact Ideal.IsMaximal.ne_top (IsLocalRing.maximalIdeal.isMaximal A) ((Ideal.eq_top_iff_one _).mpr h1)

theorem mem_of_isUnit_smul_mem {A V : Type} [CommRing A] [AddCommGroup V] [Module A V]
    (N : Submodule A V) {r : A} (hu : IsUnit r) {x : V} (h : r • x ∈ N) : x ∈ N := by
  rw [← hu.unit_spec, ← Units.smul_def] at h
  exact (N.smul_mem_iff' hu.unit).mp h

theorem exists_small_pow_sub_one {A : Type} [CommRing A] [IsLocalRing A] (ρ : GaloisRepAdic A)
    {q : ℕ} (hq : q.Prime) (P : ValuationSubring (AlgebraicClosure ℚ)) (hP : P.LiesOverPrime q)
    {σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ}
    (hwild : ∀ z : AlgebraicClosure ℚ, z ≠ 0 → σ z * z⁻¹ - 1 ∈ P.nonunits) (n : ℕ) :
    ∃ a : ℕ, Small (IsLocalRing.maximalIdeal A) n (ρ.ρ σ ^ q ^ a - 1) := by
  obtain ⟨L, hL, hcont⟩ := ρ.isAdicContinuous n
  haveI := hL
  haveI : Algebra.IsAlgebraic ℚ (AlgebraicClosure ℚ) := AlgebraicClosure.isAlgebraic ℚ
  haveI : IsAlgClosure ℚ (AlgebraicClosure ℚ) := ⟨inferInstance, inferInstance⟩
  haveI : Normal ℚ (AlgebraicClosure ℚ) := IsAlgClosure.normal ℚ (AlgebraicClosure ℚ)
  haveI : FiniteDimensional ℚ ↥(IntermediateField.normalClosure ℚ (↥L) (AlgebraicClosure ℚ)) :=
    normalClosure.is_finiteDimensional (F := ℚ) (K := ↥L) (L := AlgebraicClosure ℚ)
  haveI : Normal ℚ ↥(IntermediateField.normalClosure ℚ (↥L) (AlgebraicClosure ℚ)) :=
    normalClosure.normal (F := ℚ) (K := ↥L) (L := AlgebraicClosure ℚ)
  have hle : L ≤ IntermediateField.normalClosure ℚ (↥L) (AlgebraicClosure ℚ) := by
    have h := AlgHom.fieldRange_le_normalClosure L.val
    rwa [IntermediateField.fieldRange_val] at h
  obtain ⟨a, ha⟩ := ValuationSubring.exists_forall_pow_prime_pow_apply_eq_self_of_wild hq P hP hwild
    (IntermediateField.normalClosure ℚ (↥L) (AlgebraicClosure ℚ))
  refine ⟨a, fun v => ?_⟩
  have h1 : ρ.ρ (σ ^ (q ^ a)) v - v ∈ (IsLocalRing.maximalIdeal A ^ n) • (⊤ : Submodule A ρ.V) :=
    hcont _ (fun x hx => ha x (hle hx)) v
  have e : (ρ.ρ σ ^ q ^ a - 1) v = ρ.ρ (σ ^ (q ^ a)) v - v := by
    rw [LinearMap.sub_apply, Module.End.one_apply, map_pow]
  rw [e]
  exact h1

end WildOrder

open WildOrder in
theorem solution
    {A : Type} [CommRing A] [IsLocalRing A] [IsNoetherianRing A] (ρ : GaloisRepAdic A)
    {p : ℕ} (hp : p.Prime) (hpA : (p : A) ∈ IsLocalRing.maximalIdeal A) {q : ℕ} (hq : q.Prime) (hqp : q ≠ p)
    (P : ValuationSubring (AlgebraicClosure ℚ)) (hP : P.LiesOverPrime q)
    {σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ}
    (hwild : ∀ z : AlgebraicClosure ℚ, z ≠ 0 → σ z * z⁻¹ - 1 ∈ P.nonunits) :
    ∃ k : ℕ, ρ.ρ σ ^ q ^ k = 1 := by
  classical
  have hqA : IsUnit (q : A) := isUnit_natCast_of_prime_ne hp hq hqp hpA

  obtain ⟨a, ha1⟩ := exists_small_pow_sub_one ρ hq P hP hwild 1
  refine ⟨a, ?_⟩

  have hstab : ∀ n : ℕ, 1 ≤ n → Small (IsLocalRing.maximalIdeal A) n (ρ.ρ σ ^ q ^ a - 1) := by
    intro n hn
    induction n, hn using Nat.le_induction with
    | base => exact ha1
    | succ n hn ih =>
        obtain ⟨b, hb⟩ := exists_small_pow_sub_one ρ hq P hP hwild (n + 1)
        have e1 : (1 + (ρ.ρ σ ^ q ^ a - 1)) = ρ.ρ σ ^ q ^ a := add_sub_cancel 1 _
        have e2 : (1 + (ρ.ρ σ ^ q ^ b - 1)) = ρ.ρ σ ^ q ^ b := add_sub_cancel 1 _

        have hpow : Small (IsLocalRing.maximalIdeal A) (n + 1)
            ((1 + (ρ.ρ σ ^ q ^ a - 1)) ^ q ^ b - 1) := by
          have h := hb.one_add_pow_sub_one (q ^ a)
          rwa [e2, ← pow_mul, mul_comm, pow_mul, ← e1] at h

        have hfirst : Small (IsLocalRing.maximalIdeal A) (n + 1)
            ((1 + (ρ.ρ σ ^ q ^ a - 1)) ^ q ^ b - 1 - q ^ b • (ρ.ρ σ ^ q ^ a - 1)) :=
          (ih.one_add_pow_sub_one_sub_nsmul (q ^ b)).mono (by omega)
        have hdiff := hpow.sub hfirst
        rw [sub_sub_cancel] at hdiff

        intro v
        have hv := hdiff v
        rw [LinearMap.smul_apply, ← Nat.cast_smul_eq_nsmul A] at hv
        have hu : IsUnit (((q ^ b : ℕ)) : A) := by
          rw [Nat.cast_pow]
          exact hqA.pow _
        exact mem_of_isUnit_smul_mem _ hu hv

  refine LinearMap.ext fun v => ?_
  have hmem : (ρ.ρ σ ^ q ^ a - 1) v ∈ ⨅ n : ℕ, (IsLocalRing.maximalIdeal A ^ n) • (⊤ : Submodule A ρ.V) :=
    (Submodule.mem_iInf _).mpr fun n => (hstab (n + 1) (by omega)).mono (Nat.le_succ n) v
  rw [Ideal.iInf_pow_smul_eq_bot_of_isLocalRing _ (IsLocalRing.maximalIdeal.isMaximal A).ne_top,
    Submodule.mem_bot, LinearMap.sub_apply, Module.End.one_apply, sub_eq_zero] at hmem
  rw [hmem, Module.End.one_apply]

end S_GaloisRepAdic_exists_pow_prime_pow_eq_one_of_wild
end P2MW
export P2MW.S_GaloisRepAdic_exists_pow_prime_pow_eq_one_of_wild (solution)
