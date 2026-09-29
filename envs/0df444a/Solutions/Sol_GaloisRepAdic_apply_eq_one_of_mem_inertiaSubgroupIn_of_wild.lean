-- Prove2me | solution 1 for GaloisRepAdic.apply_eq_one_of_mem_inertiaSubgroupIn_of_wild
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.805612+00:00
-- url     : https://prove2.me/submissions/8bc28cd3-14e3-5813-9944-2512b6b6ef0e

import Mathlib
import Definitions.Def_GaloisRep_Adic
import Definitions.Def_GaloisRep_LocalConditions
import Definitions.Def_EllipticCurve_FrobeniusTrace
import Theorems.Thm_ValuationSubring_exists_forall_pow_prime_pow_apply_eq_self_of_wild
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_GaloisRepAdic_apply_eq_one_of_mem_inertiaSubgroupIn_of_wild

set_option autoImplicit false
set_option maxHeartbeats 3200000
set_option linter.unusedSectionVars false

open IsLocalRing Polynomial
open scoped TensorProduct

namespace GaloisRep
namespace Sol4fb1
p2m_open "GaloisRep"

section P
variable {R : Type} [CommRing R] {V : Type} [AddCommGroup V] [Module R V]

theorem map_smul_top_le (N : Module.End R V) (I J : Ideal R) (hN : LinearMap.range N ≤ J • (⊤ : Submodule R V)) :
    Submodule.map N (I • (⊤ : Submodule R V)) ≤ (I * J) • (⊤ : Submodule R V) := by
  rw [Submodule.map_smul'', Submodule.map_top, Submodule.mul_smul]
  exact Submodule.smul_mono le_rfl hN

theorem range_pow_sub_one_le (g : Module.End R V) (𝔪 I : Ideal R) (p : ℕ) (hp : (p : R) ∈ 𝔪)
    (hg : LinearMap.range (g - 1) ≤ I • (⊤ : Submodule R V)) :
    LinearMap.range (g ^ p - 1) ≤ (𝔪 * I ⊔ I * I) • (⊤ : Submodule R V) := by

  have hgeom : g ^ p - 1 = ((Finset.range p).sum fun i => g ^ i) * (g - 1) := (geom_sum_mul g p).symm

  have hgi : ∀ i : ℕ, LinearMap.range (g ^ i - 1) ≤ I • (⊤ : Submodule R V) := by
    intro i
    rw [← mul_geom_sum g i, Module.End.mul_eq_comp]
    exact (LinearMap.range_comp_le_range _ _).trans hg
  rintro _ ⟨v, rfl⟩
  rw [hgeom, Module.End.mul_apply]
  set w := (g - 1) v with hw
  have hwI : w ∈ I • (⊤ : Submodule R V) := hg ⟨v, rfl⟩

  have hdec : ((Finset.range p).sum fun i => g ^ i) w = (p : R) • w + (Finset.range p).sum (fun i => (g ^ i - 1) w) := by
    rw [LinearMap.sum_apply]
    simp only [LinearMap.sub_apply, Module.End.one_apply, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_range,
      ← Nat.cast_smul_eq_nsmul R]
    abel
  rw [hdec]
  refine Submodule.add_mem _ ?_ (Submodule.sum_mem _ fun i _ => ?_)
  ·
    refine Submodule.smul_mono (le_sup_left : 𝔪 * I ≤ 𝔪 * I ⊔ I * I) le_rfl ?_
    rw [Submodule.mul_smul]
    exact Submodule.smul_mem_smul hp hwI
  ·
    refine Submodule.smul_mono (le_sup_right : I * I ≤ 𝔪 * I ⊔ I * I) le_rfl ?_
    exact map_smul_top_le (g ^ i - 1) I I (hgi i) ⟨w, hwI, rfl⟩

theorem pow_prime_pow_sub_one_range_le (𝔪 : Ideal R) {p : ℕ} (hpm : (p : R) ∈ 𝔪) (f : Module.End R V)
    (hf : LinearMap.range (f - 1) ≤ 𝔪 • (⊤ : Submodule R V)) (n : ℕ) :
    LinearMap.range (f ^ (p ^ n) - 1) ≤ 𝔪 ^ (n + 1) • (⊤ : Submodule R V) := by
  induction n with
  | zero => simpa using hf
  | succ n ih =>
    rw [pow_succ, pow_mul]
    refine (range_pow_sub_one_le (f ^ (p ^ n)) 𝔪 (𝔪 ^ (n + 1)) p hpm ih).trans (Submodule.smul_mono ?_ le_rfl)
    refine sup_le ?_ ?_
    · rw [← pow_succ']
    · rw [← pow_add]
      exact Ideal.pow_le_pow_right (by omega)

end P

theorem eq_zero_of_forall_range_le_pow_smul {R : Type} [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
    {V : Type} [AddCommGroup V] [Module R V] [Module.Finite R V] (g : Module.End R V)
    (hg : ∀ n : ℕ, LinearMap.range g ≤ (maximalIdeal R) ^ n • (⊤ : Submodule R V)) : g = 0 := by
  refine LinearMap.ext fun v => ?_
  have hv : g v ∈ (⨅ n : ℕ, (maximalIdeal R) ^ n • (⊤ : Submodule R V)) :=
    Submodule.mem_iInf _ |>.mpr fun n => hg n ⟨v, rfl⟩
  rw [Ideal.iInf_pow_smul_eq_bot_of_isLocalRing _ (maximalIdeal.isMaximal R).ne_top, Submodule.mem_bot] at hv
  rw [hv, LinearMap.zero_apply]

theorem range_sub_one_le_of_pow_of_pow {R : Type} [CommRing R] {V : Type} [AddCommGroup V] [Module R V]
    (f : Module.End R V) (W : Submodule R V) (hW : W ≤ W.comap f) {a b : ℕ} (hab : Nat.Coprime a b)
    (ha : LinearMap.range (f ^ a - 1) ≤ W) (hb : LinearMap.range (f ^ b - 1) ≤ W) :
    LinearMap.range (f - 1) ≤ W := by

  let fq : Module.End R (V ⧸ W) := W.mapQ W f hW
  have hq : ∀ k : ℕ, LinearMap.range (f ^ k - 1) ≤ W → fq ^ k = 1 := by
    intro k hk
    rw [← Submodule.mapQ_pow W hW k]
    refine LinearMap.ext fun x => ?_
    induction x using Submodule.Quotient.induction_on with
    | H v =>
      rw [Submodule.mapQ_apply, Module.End.one_apply, Submodule.Quotient.eq]
      exact hk ⟨v, by simp⟩
  have h1 : fq = 1 := by
    have h := (pow_gcd_eq_one (a := fq) (m := a) (n := b)).mpr ⟨hq a ha, hq b hb⟩
    rwa [Nat.Coprime.gcd_eq_one hab, pow_one] at h
  rintro _ ⟨v, rfl⟩
  have hv : fq (Submodule.Quotient.mk v) = Submodule.Quotient.mk v := by rw [h1, Module.End.one_apply]
  rw [Submodule.mapQ_apply, Submodule.Quotient.eq] at hv
  simpa using hv

end GaloisRep.Sol4fb1

open GaloisRep.Sol4fb1 in
theorem solution
    {R : Type} [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
    (ρ : GaloisRepAdic R) {p : ℕ} (hp : p.Prime) (hpR : (p : R) ∈ maximalIdeal R) {q : ℕ} (hq : q.Prime)
    (hqp : q ≠ p) (hunr : ρ.residual.IsUnramifiedAt q) (P : ValuationSubring (AlgebraicClosure ℚ))
    (hP : P.LiesOverPrime q) {σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ} (hσ : σ ∈ P.inertiaSubgroupIn ℚ)
    (hwild : ∀ z : AlgebraicClosure ℚ, z ≠ 0 → σ z * z⁻¹ - 1 ∈ P.nonunits) :
    ρ.ρ σ = 1 := by
  classical

  have h1 : LinearMap.range (ρ.ρ σ - 1) ≤ (maximalIdeal R) • (⊤ : Submodule R ρ.V) := by
    have hres : ρ.residual.ρ σ = 1 := hunr P hP σ hσ
    rintro _ ⟨v, rfl⟩
    have hv := congrArg (fun f => f ((1 : ResidueField R) ⊗ₜ[R] v)) hres
    change ((ρ.ρ σ).baseChange (ResidueField R)) ((1 : ResidueField R) ⊗ₜ[R] v) = (1 : ResidueField R) ⊗ₜ[R] v at hv
    rw [LinearMap.baseChange_tmul, ← sub_eq_zero, ← TensorProduct.tmul_sub] at hv

    have hv' : ((Ideal.Quotient.mk (maximalIdeal R) 1) ⊗ₜ[R] (ρ.ρ σ v - v) : (R ⧸ maximalIdeal R) ⊗[R] ρ.V) = 0 := hv
    have h := congrArg (TensorProduct.quotTensorEquivQuotSMul ρ.V (maximalIdeal R)) hv'
    rw [LinearEquiv.map_zero, TensorProduct.quotTensorEquivQuotSMul_mk_tmul, one_smul, Submodule.Quotient.mk_eq_zero] at h
    simpa using h

  have hn : ∀ n : ℕ, LinearMap.range (ρ.ρ σ - 1) ≤ (maximalIdeal R) ^ (n + 1) • (⊤ : Submodule R ρ.V) := by
    intro n

    obtain ⟨L, hLfin, hL⟩ := ρ.isAdicContinuous (n + 1)
    haveI := hLfin
    haveI : IsAlgClosure ℚ (AlgebraicClosure ℚ) := AlgebraicClosure.instIsAlgClosure ℚ
    haveI : Normal ℚ (AlgebraicClosure ℚ) := IsAlgClosure.normal ℚ (AlgebraicClosure ℚ)
    let F : IntermediateField ℚ (AlgebraicClosure ℚ) := IntermediateField.normalClosure ℚ L (AlgebraicClosure ℚ)
    haveI : Normal ℚ F := normalClosure.normal ℚ L (AlgebraicClosure ℚ)
    have hLF : L ≤ F := IntermediateField.le_normalClosure L
    have hF : ∀ g : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ, (∀ x ∈ F, g x = x) →
        LinearMap.range (ρ.ρ g - 1) ≤ (maximalIdeal R) ^ (n + 1) • (⊤ : Submodule R ρ.V) := by
      intro g hg
      rintro _ ⟨v, rfl⟩
      exact hL g (fun x hx => hg x (hLF hx)) v
    obtain ⟨a, ha⟩ := ValuationSubring.exists_forall_pow_prime_pow_apply_eq_self_of_wild hq P hP hwild F
    have hqa : LinearMap.range (ρ.ρ σ ^ (q ^ a) - 1) ≤ (maximalIdeal R) ^ (n + 1) • (⊤ : Submodule R ρ.V) := by
      rw [← map_pow]; exact hF _ ha
    have hpa : LinearMap.range (ρ.ρ σ ^ (p ^ n) - 1) ≤ (maximalIdeal R) ^ (n + 1) • (⊤ : Submodule R ρ.V) :=
      pow_prime_pow_sub_one_range_le (maximalIdeal R) hpR (ρ.ρ σ) h1 n
    refine range_sub_one_le_of_pow_of_pow (ρ.ρ σ) _ ?_ ?_ hqa hpa
    ·
      intro x hx
      rw [Submodule.mem_comap]
      exact map_smul_top_le (ρ.ρ σ) _ ⊤ (by simp) ⟨x, hx, rfl⟩ |> fun h => by simpa [Ideal.mul_top] using h
    · exact Nat.Coprime.pow _ _ ((Nat.coprime_primes hq hp).mpr hqp)

  have h0 : ρ.ρ σ - 1 = 0 := eq_zero_of_forall_range_le_pow_smul (ρ.ρ σ - 1) (fun n => by
    cases n with
    | zero => simp
    | succ n => exact hn n)
  exact sub_eq_zero.mp h0

end S_GaloisRepAdic_apply_eq_one_of_mem_inertiaSubgroupIn_of_wild
end P2MW
export P2MW.S_GaloisRepAdic_apply_eq_one_of_mem_inertiaSubgroupIn_of_wild (solution)
