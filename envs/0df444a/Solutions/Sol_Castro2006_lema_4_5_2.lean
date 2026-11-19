-- Prove2me | solution 1 for Castro2006.lema_4_5_2
-- status  : ACCEPTED   (prove)
-- author  : @garyholm
-- created : 2026-11-18T21:26:24.812555+00:00
-- url     : https://prove2.me/submissions/64809a6e-4cee-4367-84ea-0c7e8bbb80d0

import Mathlib

theorem solution {p : ℕ} (hp : p.Prime) (a : ℤ) (n : ℕ) (hn : 2 ≤ n)
    (hap : a ^ p ≡ 1 [ZMOD p ^ n]) (ha1 : ¬(a ≡ 1 [ZMOD p ^ n])) :
    (p ≠ 2 → a ≡ 1 [ZMOD p ^ (n - 1)]) ∧
    (p = 2 → (a ≡ 1 [ZMOD 2 ^ (n - 1)] ∨ a ≡ -1 [ZMOD 2 ^ (n - 1)])) := by
  have hdvd : ((p : ℤ)) ^ n ∣ a ^ p - 1 := by
    have := (Int.ModEq.dvd hap.symm)
    simpa using this
  constructor
  · intro hp2
    have hodd : Odd p := hp.odd_of_ne_two hp2
    have hp1 : (p : ℤ) ∣ a ^ p - 1 :=
      dvd_trans (dvd_pow_self _ (by omega)) hdvd
    have hfer : (p : ℤ) ∣ a - a ^ p := by
      have := Fact.mk hp
      rw [← ZMod.intCast_eq_intCast_iff_dvd_sub]
      push_cast
      exact ZMod.pow_card _
    have hpa1 : (p : ℤ) ∣ a - 1 := by
      have := dvd_add hfer hp1
      simpa using this
    have hpa : ¬ (p : ℤ) ∣ a := by
      intro h
      have h1 : (p : ℤ) ∣ 1 := by
        have := dvd_sub h hpa1
        simpa using this
      have : p ∣ 1 := by exact_mod_cast h1
      exact hp.one_lt.ne' (Nat.dvd_one.mp this)
    have hlte := Int.emultiplicity_pow_sub_pow hp hodd hpa1 hpa p
    rw [one_pow, Nat.Prime.emultiplicity_self hp] at hlte
    have hle : (n : ℕ∞) ≤ emultiplicity (p : ℤ) (a ^ p - 1) := le_emultiplicity_of_pow_dvd hdvd
    rw [hlte] at hle
    have h2 : ((n - 1 : ℕ) : ℕ∞) + 1 ≤ emultiplicity (p : ℤ) (a - 1) + 1 := by
      have : ((n - 1 : ℕ) : ℕ∞) + 1 = (n : ℕ∞) := by
        have hn1 : n - 1 + 1 = n := by omega
        exact_mod_cast hn1
      rw [this]; exact hle
    have h3 : ((n - 1 : ℕ) : ℕ∞) ≤ emultiplicity (p : ℤ) (a - 1) :=
      (ENat.add_le_add_iff_right ENat.one_ne_top).mp h2
    have h4 : (p : ℤ) ^ (n - 1) ∣ a - 1 := pow_dvd_of_le_emultiplicity h3
    exact (Int.modEq_iff_dvd.mpr h4).symm
  · intro hp2
    subst hp2
    have h2 : (2 : ℤ) ∣ a ^ 2 - 1 := dvd_trans (dvd_pow_self _ (by omega)) hdvd
    have hao : Odd a := by
      by_contra he
      rw [Int.not_odd_iff_even] at he
      obtain ⟨k, rfl⟩ := he
      have : (2 : ℤ) ∣ 1 := by
        have h' : (2:ℤ) ∣ (k + k) ^ 2 := ⟨2 * k ^ 2, by ring⟩
        have := dvd_sub h' h2
        simpa using this
      omega
    obtain ⟨k, rfl⟩ := hao
    have hm : ((2 : ℕ) : ℤ) ^ n = 4 * 2 ^ (n - 2) := by
      rw [show n = (n - 2) + 2 by omega, pow_add]
      simp; ring_nf
    have hk : (2 : ℤ) ^ (n - 2) ∣ k * (k + 1) := by
      rw [hm] at hdvd
      have : (2 * k + 1) ^ 2 - 1 = 4 * (k * (k + 1)) := by ring
      rw [this] at hdvd
      exact (mul_dvd_mul_iff_left (by norm_num : (4:ℤ) ≠ 0)).mp hdvd
    have hpow : (2 : ℤ) ^ (n - 1) = 2 * 2 ^ (n - 2) := by
      rw [show n - 1 = (n - 2) + 1 by omega, pow_succ]; ring
    rcases Int.even_or_odd k with ⟨j, hj⟩ | ⟨j, hj⟩
    · left
      have hc : IsCoprime ((2 : ℤ) ^ (n - 2)) (k + 1) := by
        apply IsCoprime.pow_left
        exact ⟨-j, 1, by rw [hj]; ring⟩
      have h5 : (2 : ℤ) ^ (n - 2) ∣ k := hc.dvd_of_dvd_mul_right hk
      have h6 : (2 : ℤ) ^ (n - 1) ∣ (2 * k + 1) - 1 := by
        rw [hpow, show (2 * k + 1) - 1 = 2 * k by ring]
        exact mul_dvd_mul_left 2 h5
      exact (Int.modEq_iff_dvd.mpr h6).symm
    · right
      have hc : IsCoprime ((2 : ℤ) ^ (n - 2)) k := by
        apply IsCoprime.pow_left
        exact ⟨-j, 1, by rw [hj]; ring⟩
      have h5 : (2 : ℤ) ^ (n - 2) ∣ k + 1 := hc.dvd_of_dvd_mul_left hk
      have h6 : (2 : ℤ) ^ (n - 1) ∣ (2 * k + 1) - (-1) := by
        rw [hpow, show (2 * k + 1) - (-1) = 2 * (k + 1) by ring]
        exact mul_dvd_mul_left 2 h5
      exact (Int.modEq_iff_dvd.mpr h6).symm
