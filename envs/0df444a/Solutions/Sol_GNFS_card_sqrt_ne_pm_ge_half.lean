-- Prove2me | solution 1 for GNFS.card_sqrt_ne_pm_ge_half
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-17T03:55:25.789575+00:00
-- url     : https://prove2.me/submissions/fe65bb87-510d-4a41-b2a1-8a500efa1968

import Mathlib
import Definitions.Def_GNFS_defs

namespace GNFSSqrt

lemma ne_neg_of_unit {R : Type*} [CommRing R] (h2 : IsUnit (2 : R)) (hnt : (0 : R) ≠ 1)
    (z : R) (hz : IsUnit z) : z ≠ -z := by
  intro h
  have : 2 * z = 0 := by linear_combination h
  have hz0 : z = 0 := (h2.mul_right_eq_zero).mp this
  rw [hz0, isUnit_zero_iff] at hz
  exact hnt hz

lemma count {R : Type*} [CommRing R] [Fintype R] [DecidableEq R] (x u : R) (hx : IsUnit x)
    (h2 : IsUnit (2 : R)) (hu2 : u ^ 2 = 1) (hu1 : u ≠ 1) (hum : u ≠ -1) :
    (Finset.univ.filter fun y : R => y ^ 2 = x ^ 2).card ≤
      2 * (Finset.univ.filter fun y : R => y ^ 2 = x ^ 2 ∧ y ≠ x ∧ y ≠ -x).card := by
  have hnt : (0 : R) ≠ 1 := by
    intro h; apply hu1
    calc u = u * 1 := (mul_one u).symm
      _ = 1 := by rw [← h, mul_zero, h]
  have hxu : IsUnit (x * u) := hx.mul (IsUnit.of_pow_eq_one hu2 (by norm_num))
  have hx_ne := ne_neg_of_unit h2 hnt x hx
  have hxu_ne := ne_neg_of_unit h2 hnt (x * u) hxu
  set R0 := Finset.univ.filter fun y : R => y ^ 2 = x ^ 2
  set T := Finset.univ.filter fun y : R => y ^ 2 = x ^ 2 ∧ y ≠ x ∧ y ≠ -x
  have hsplit := Finset.card_filter_add_card_filter_not
    (s := R0) (fun y : R => y ≠ x ∧ y ≠ -x)
  have hT : R0.filter (fun y : R => y ≠ x ∧ y ≠ -x) = T := by
    ext y; simp [R0, T, and_assoc]
  have hpair : R0.filter (fun y : R => ¬ (y ≠ x ∧ y ≠ -x)) = {x, -x} := by
    ext y
    simp only [R0, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert,
      Finset.mem_singleton, not_and_or, not_not]
    constructor
    · rintro ⟨_, h | h⟩
      · left; exact h
      · right; exact h
    · rintro (h | h)
      · exact ⟨by rw [h], Or.inl h⟩
      · exact ⟨by rw [h]; ring, Or.inr h⟩
  rw [hT, hpair, Finset.card_pair hx_ne] at hsplit
  have hsub : ({x * u, -(x * u)} : Finset R) ⊆ T := by
    intro y hy
    simp only [Finset.mem_insert, Finset.mem_singleton] at hy
    simp only [T, Finset.mem_filter, Finset.mem_univ, true_and]
    have c1 : x * u ≠ x := by
      intro h; apply hu1
      exact hx.mul_left_cancel (by rw [h, mul_one])
    have c2 : x * u ≠ -x := by
      intro h; apply hum
      exact hx.mul_left_cancel (by rw [h]; ring)
    rcases hy with rfl | rfl
    · refine ⟨by rw [mul_pow, hu2, mul_one], c1, c2⟩
    · refine ⟨by rw [neg_sq, mul_pow, hu2, mul_one], fun h => c2 ?_, fun h => c1 ?_⟩
      · linear_combination -h
      · linear_combination -h
  have h2T := Finset.card_le_card hsub
  rw [Finset.card_pair hxu_ne] at h2T
  omega

end GNFSSqrt

namespace GNFSSqrt

lemma decomp (n : ℕ) (hn : n ≠ 0) (hodd : Odd n) (hk : 2 ≤ n.primeFactors.card) :
    ∃ a b : ℕ, a * b = n ∧ Nat.Coprime a b ∧ 2 < a ∧ 2 < b := by
  obtain ⟨p, hp, q, hq, hpq⟩ := Finset.one_lt_card.mp (by omega : 1 < n.primeFactors.card)
  have hpp := Nat.prime_of_mem_primeFactors hp
  have hqp := Nat.prime_of_mem_primeFactors hq
  have hpn := Nat.dvd_of_mem_primeFactors hp
  have hqn := Nat.dvd_of_mem_primeFactors hq
  have hp2 : p ≠ 2 := by
    rintro rfl; exact (Nat.not_even_iff_odd.mpr hodd) (even_iff_two_dvd.mpr hpn)
  have hq2 : q ≠ 2 := by
    rintro rfl; exact (Nat.not_even_iff_odd.mpr hodd) (even_iff_two_dvd.mpr hqn)
  have hp3 : 3 ≤ p := by have := hpp.two_le; omega
  have hq3 : 3 ≤ q := by have := hqp.two_le; omega
  set k := n.factorization p
  have hk1 : 1 ≤ k := hpp.factorization_pos_of_dvd hn hpn
  refine ⟨p ^ k, n / p ^ k, Nat.ordProj_mul_ordCompl_eq_self n p,
    Nat.Coprime.pow_left k (Nat.coprime_ordCompl hpp hn), ?_, ?_⟩
  · calc 2 < p := by omega
      _ = p ^ 1 := (pow_one p).symm
      _ ≤ p ^ k := Nat.pow_le_pow_right hpp.pos hk1
  · have hqb : q ∣ n / p ^ k := by
      have hmul : q ∣ p ^ k * (n / p ^ k) := by rw [Nat.ordProj_mul_ordCompl_eq_self]; exact hqn
      rcases (Nat.Prime.dvd_mul hqp).mp hmul with h | h
      · exact absurd ((Nat.prime_dvd_prime_iff_eq hqp hpp).mp (hqp.dvd_of_dvd_pow h)) (Ne.symm hpq)
      · exact h
    have hb0 : 0 < n / p ^ k := Nat.pos_of_ne_zero (fun h => by
      have := Nat.ordProj_mul_ordCompl_eq_self n p
      rw [h, mul_zero] at this; exact hn this.symm)
    have := Nat.le_of_dvd hb0 hqb
    omega

end GNFSSqrt

open GNFSSqrt in
theorem solution (n : ℕ) [NeZero n] (hodd : Odd n)
    (hk : 2 ≤ n.primeFactors.card) (x : ZMod n) (hx : IsUnit x) :
    (Finset.univ.filter fun y : ZMod n => y ^ 2 = x ^ 2).card ≤
      2 * (Finset.univ.filter fun y : ZMod n => y ^ 2 = x ^ 2 ∧ y ≠ x ∧ y ≠ -x).card := by
  have h2 : IsUnit (2 : ZMod n) := by
    have : IsUnit ((2 : ℕ) : ZMod n) :=
      (ZMod.unitOfCoprime 2 (Nat.coprime_two_left.mpr hodd)).isUnit
    simpa using this
  obtain ⟨a, b, hab, hcop, ha, hb⟩ := decomp n (NeZero.ne n) hodd hk
  subst hab
  have : Fact (2 < a) := ⟨ha⟩
  have : Fact (2 < b) := ⟨hb⟩
  set e := ZMod.chineseRemainder hcop
  set u : ZMod (a * b) := e.symm (1, -1)
  have hu2 : u ^ 2 = 1 := by
    apply e.injective
    rw [map_pow, map_one]
    simp [u]
  have hu1 : u ≠ 1 := by
    intro h
    have := congrArg e h
    simp only [u, RingEquiv.apply_symm_apply, map_one, Prod.mk_eq_one] at this
    exact ZMod.neg_one_ne_one this.2
  have hum : u ≠ -1 := by
    intro h
    have := congrArg e h
    simp only [u, RingEquiv.apply_symm_apply, map_neg, map_one] at this
    have h1 := congrArg Prod.fst this
    simp only [Prod.fst_neg, Prod.fst_one] at h1
    exact ZMod.neg_one_ne_one h1.symm
  exact count x u hx h2 hu2 hu1 hum
