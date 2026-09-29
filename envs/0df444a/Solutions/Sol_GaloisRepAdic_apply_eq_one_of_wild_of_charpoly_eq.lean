-- Prove2me | solution 1 for GaloisRepAdic.apply_eq_one_of_wild_of_charpoly_eq
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.805612+00:00
-- url     : https://prove2.me/submissions/ef159f59-b321-5fd6-8ce1-0c4bedf55882

import Definitions.Def_GaloisRep_Adic
import Theorems.Thm_ValuationSubring_exists_forall_pow_prime_pow_apply_eq_self_of_wild
import Mathlib.RingTheory.Filtration
import Mathlib.FieldTheory.Normal.Closure
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_GaloisRepAdic_apply_eq_one_of_wild_of_charpoly_eq

set_option autoImplicit false
open Polynomial

namespace WildUnipotent

private theorem pow_apply_eq_add_smul {A V : Type} [CommRing A] [AddCommGroup V] [Module A V]
    (T : Module.End A V) (hT : (T - 1) * (T - 1) = 0) (k : ℕ) (w : V) :
    (T ^ k) w = w + (k : A) • ((T - 1) w) := by
  induction k generalizing w with
  | zero => simp
  | succ k ih =>
      have hTT : ∀ x : V, (T - 1) ((T - 1) x) = 0 := fun x => by
        have h := congrArg (fun S : Module.End A V => S x) hT
        simpa only [Module.End.mul_apply, LinearMap.zero_apply] using h
      have hTx : ∀ x : V, T x = x + (T - 1) x := fun x => by
        rw [LinearMap.sub_apply, Module.End.one_apply]
        abel
      calc (T ^ (k + 1)) w = T ((T ^ k) w) := by rw [pow_succ', Module.End.mul_apply]
        _ = T (w + (k : A) • (T - 1) w) := by rw [ih]
        _ = T w + (k : A) • T ((T - 1) w) := by rw [map_add, map_smul]
        _ = (w + (T - 1) w) + (k : A) • ((T - 1) w + (T - 1) ((T - 1) w)) := by rw [← hTx, ← hTx]
        _ = w + ((k : A) + 1) • (T - 1) w := by
            rw [hTT, add_zero, add_smul, one_smul]
            abel
        _ = w + ((k + 1 : ℕ) : A) • (T - 1) w := by rw [Nat.cast_succ]

private theorem isUnit_natCast_of_prime_ne {A : Type} [CommRing A] [IsLocalRing A] {p q : ℕ} (hp : p.Prime)
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

private theorem mem_of_isUnit_smul_mem {A V : Type} [CommRing A] [AddCommGroup V] [Module A V]
    (N : Submodule A V) {r : A} (hu : IsUnit r) {x : V} (h : r • x ∈ N) : x ∈ N := by
  rw [← hu.unit_spec, ← Units.smul_def] at h
  exact (N.smul_mem_iff' hu.unit).mp h

end WildUnipotent

theorem solution
    {A : Type} [CommRing A] [IsLocalRing A] [IsNoetherianRing A] (ρ : GaloisRepAdic A)
    {p : ℕ} (hp : p.Prime) (hpA : (p : A) ∈ IsLocalRing.maximalIdeal A) {q : ℕ} (hq : q.Prime) (hqp : q ≠ p)
    (P : ValuationSubring (AlgebraicClosure ℚ)) (hP : P.LiesOverPrime q)
    {σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ}
    (hwild : ∀ z : AlgebraicClosure ℚ, z ≠ 0 → σ z * z⁻¹ - 1 ∈ P.nonunits)
    (hchar : LinearMap.charpoly (ρ.ρ σ) = (X - 1) ^ 2) :
    ρ.ρ σ = 1 := by
  classical
  have hsq : (ρ.ρ σ - 1) ^ 2 = 0 := by
    have h := LinearMap.aeval_self_charpoly (ρ.ρ σ)
    rw [hchar] at h
    simpa using h
  have hN : (ρ.ρ σ - 1) * (ρ.ρ σ - 1) = 0 := by rwa [pow_two] at hsq
  have hqA : IsUnit (q : A) := WildUnipotent.isUnit_natCast_of_prime_ne hp hq hqp hpA
  have hlevel : ∀ n : ℕ, ∀ v : ρ.V,
      (ρ.ρ σ - 1) v ∈ (IsLocalRing.maximalIdeal A ^ n) • (⊤ : Submodule A ρ.V) := by
    intro n v
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
    have h1 : ρ.ρ (σ ^ (q ^ a)) v - v ∈ (IsLocalRing.maximalIdeal A ^ n) • (⊤ : Submodule A ρ.V) :=
      hcont _ (fun x hx => ha x (hle hx)) v
    rw [map_pow, WildUnipotent.pow_apply_eq_add_smul (ρ.ρ σ) hN, add_sub_cancel_left] at h1
    have hu : IsUnit (((q ^ a : ℕ)) : A) := by
      rw [Nat.cast_pow]
      exact hqA.pow _
    exact WildUnipotent.mem_of_isUnit_smul_mem _ hu h1
  refine LinearMap.ext fun v => ?_
  have hmem : (ρ.ρ σ - 1) v ∈ ⨅ n : ℕ, (IsLocalRing.maximalIdeal A ^ n) • (⊤ : Submodule A ρ.V) :=
    (Submodule.mem_iInf _).mpr fun n => hlevel n v
  rw [Ideal.iInf_pow_smul_eq_bot_of_isLocalRing _ (IsLocalRing.maximalIdeal.isMaximal A).ne_top,
    Submodule.mem_bot, LinearMap.sub_apply, Module.End.one_apply, sub_eq_zero] at hmem
  rw [hmem, Module.End.one_apply]

end S_GaloisRepAdic_apply_eq_one_of_wild_of_charpoly_eq
end P2MW
export P2MW.S_GaloisRepAdic_apply_eq_one_of_wild_of_charpoly_eq (solution)
