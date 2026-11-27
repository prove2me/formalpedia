-- Prove2me | solution 1 for Erdos287.pocklington_prime_certificate
-- status  : ACCEPTED   (prove)
-- author  : @immiq
-- created : 2026-11-26T22:16:25.216855+00:00
-- url     : https://prove2.me/submissions/bcdcb275-eb55-4c67-a372-e905f11b047f

import Mathlib

set_option autoImplicit false

/-- Pocklington's primality criterion with the unit test written in ZMod. -/
theorem solution (n F : ℕ) (hn : 1 < n) (hF : 0 < F) (hdiv : F ∣ n - 1)
    (hsize : n < F ^ 2)
    (hw : ∀ d : ℕ, d.Prime → d ∣ F → ∃ a : ℕ,
      (a : ZMod n) ^ (n - 1) = 1 ∧ IsUnit ((a : ZMod n) ^ ((n - 1) / d) - 1)) :
    n.Prime := by
  by_contra hnp
  let p := n.minFac
  have hp : p.Prime := Nat.minFac_prime (by omega)
  have hpn : p ∣ n := Nat.minFac_dvd n
  let _ : Fact p.Prime := ⟨hp⟩
  let φ := ZMod.castHom hpn (ZMod p)
  have hL : 0 < n - 1 := by omega
  have hpL : 0 < p - 1 := by have := hp.one_lt; omega
  have hFdivp : F ∣ p - 1 := by
    apply (Nat.factorization_le_iff_dvd hF.ne' hpL.ne').mp
    intro d
    by_contra! htoo
    have hdFpos : 1 ≤ F.factorization d := by omega
    have hd : d.Prime := by
      by_contra h
      simp [Nat.factorization_eq_zero_of_not_prime F h] at hdFpos
    have hdF : d ∣ F := (hd.dvd_iff_one_le_factorization hF.ne').mpr hdFpos
    obtain ⟨a, ha, hu⟩ := hw d hd hdF
    have hafull : (a : ZMod p) ^ (n - 1) = 1 := by
      simpa only [map_pow, map_natCast, map_one] using congrArg φ ha
    have hanot : (a : ZMod p) ^ ((n - 1) / d) ≠ 1 := by
      have hne := (hu.map φ).ne_zero
      simp only [map_sub, map_pow, map_natCast, map_one] at hne
      exact sub_ne_zero.mp hne
    have ha0 : (a : ZMod p) ≠ 0 := by
      intro he
      rw [he, zero_pow hL.ne'] at hafull
      exact zero_ne_one hafull
    let o := orderOf (a : ZMod p)
    have hoL : o ∣ n - 1 := orderOf_dvd_iff_pow_eq_one.mpr hafull
    have hop : o ∣ p - 1 :=
      orderOf_dvd_iff_pow_eq_one.mpr (ZMod.pow_card_sub_one_eq_one ha0)
    have ho0 : o ≠ 0 := by
      intro he
      rw [he, zero_dvd_iff] at hoL
      exact hL.ne' hoL
    have hop' := (Nat.factorization_le_iff_dvd ho0 hpL.ne').mpr hop d
    have hFL := (Nat.factorization_le_iff_dvd hF.ne' hL.ne').mpr hdiv d
    obtain ⟨k, hk⟩ := hoL
    have hk0 : k ≠ 0 := by
      intro he
      rw [he, mul_zero] at hk
      exact hL.ne' hk
    have hfac : (n - 1).factorization d = o.factorization d + k.factorization d := by
      rw [hk, Nat.factorization_mul ho0 hk0, Finsupp.add_apply]
    have hdk : d ∣ k := (hd.dvd_iff_one_le_factorization hk0).mpr (by omega)
    obtain ⟨j, rfl⟩ := hdk
    have hquot : (n - 1) / d = o * j := by
      rw [hk, show o * (d * j) = (o * j) * d by ring, Nat.mul_div_cancel _ hd.pos]
    exact hanot (orderOf_dvd_iff_pow_eq_one.mp (show o ∣ (n - 1) / d from
      ⟨j, hquot⟩))
  have hFp := Nat.le_of_dvd hpL hFdivp
  have hsquare := Nat.pow_le_pow_left (show F ≤ p by omega) 2
  exact (not_lt_of_ge (hsquare.trans (Nat.minFac_sq_le_self (by omega) hnp))) hsize

