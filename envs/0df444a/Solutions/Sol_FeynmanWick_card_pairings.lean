-- Prove2me | solution 1 for FeynmanWick.card_pairings
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-24T07:13:39.404985+00:00
-- url     : https://prove2.me/submissions/bc0501e6-99b4-4e1e-968c-af551b532fd1

import Mathlib
import Definitions.Def_FeynmanWickPairings

open MeasureTheory ProbabilityTheory
open FeynmanWick

theorem W7b_FeynmanWick_iff {n : ℕ} (σ : Equiv.Perm (Fin (2 * n))) :
    IsPairing σ ↔ σ.cycleType = Multiset.replicate n 2 := by
  classical
  constructor
  · rintro ⟨h1, h2⟩
    have hsq : σ ^ 2 = 1 := by
      ext i; simp [pow_two, h1]
    haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    have hct := Equiv.Perm.cycleType_of_pow_prime_eq_one (p := 2) hsq
    have hsupp : σ.support = Finset.univ := by
      ext i; simp [Equiv.Perm.mem_support, h2 i]
    have hsum := σ.sum_cycleType
    rw [hsupp, Finset.card_univ, Fintype.card_fin, hct, Multiset.sum_replicate, smul_eq_mul] at hsum
    rw [hct]
    congr 1
    omega
  · intro h
    have hord : orderOf σ ∣ 2 := by
      rw [← Equiv.Perm.lcm_cycleType, h]
      apply Multiset.lcm_dvd.mpr
      intro b hb
      rw [Multiset.eq_of_mem_replicate hb]
    have hsq : σ ^ 2 = 1 := orderOf_dvd_iff_pow_eq_one.mp hord
    have hsum := σ.sum_cycleType
    rw [h, Multiset.sum_replicate, smul_eq_mul] at hsum
    have hsupp : σ.support = Finset.univ := by
      apply Finset.eq_univ_of_card
      rw [Fintype.card_fin]; omega
    refine ⟨fun i => ?_, fun i => ?_⟩
    · have := congrArg (fun τ : Equiv.Perm (Fin (2 * n)) => τ i) hsq
      simpa [pow_two] using this
    · have : i ∈ σ.support := by rw [hsupp]; exact Finset.mem_univ i
      exact Equiv.Perm.mem_support.mp this

theorem solution (n : ℕ) :
    (pairings n).card = Nat.doubleFactorial (2 * n - 1) := by
  classical
  have hp : pairings n = (Finset.univ.filter
      (fun g : Equiv.Perm (Fin (2 * n)) => g.cycleType = Multiset.replicate n 2)) := by
    unfold pairings
    ext σ
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    convert W7b_FeynmanWick_iff σ
  have key := Equiv.Perm.card_of_cycleType_mul_eq (Fin (2 * n)) (Multiset.replicate n 2)
  rw [← hp] at key
  simp only [Fintype.card_fin, Multiset.sum_replicate, smul_eq_mul, Multiset.prod_replicate] at key
  rw [if_pos ⟨by omega, fun a ha => by rw [Multiset.eq_of_mem_replicate ha]⟩] at key
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp at key; simpa using key
  · have hts : (Multiset.replicate n 2).toFinset = {2} := by
      ext a; simp only [Multiset.mem_toFinset, Multiset.mem_replicate, Finset.mem_singleton]; omega
    rw [hts, Finset.prod_singleton, Multiset.count_replicate_self, Nat.mul_comm n 2,
      Nat.sub_self, Nat.factorial_zero, one_mul] at key
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
    have h2 : 2 * (m + 1) = (2 * m + 1) + 1 := by ring
    have hf := Nat.factorial_eq_mul_doubleFactorial (2 * m + 1)
    have hd := Nat.doubleFactorial_two_mul (m + 1)
    rw [← h2, hd] at hf
    have h3 : 2 * (m + 1) - 1 = 2 * m + 1 := by omega
    rw [h3]
    have hpos : 0 < 2 ^ (m + 1) * (m + 1).factorial := by positivity
    rw [hf] at key
    have : (pairings (m + 1)).card * (2 ^ (m + 1) * (m + 1).factorial) =
        (2 * m + 1).doubleFactorial * (2 ^ (m + 1) * (m + 1).factorial) := by
      rw [key]; ring
    exact Nat.eq_of_mul_eq_mul_right hpos this
