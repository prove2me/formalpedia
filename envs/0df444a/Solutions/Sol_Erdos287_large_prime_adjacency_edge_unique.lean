-- Prove2me | solution 1 for Erdos287.large_prime_adjacency_edge_unique
-- status  : ACCEPTED   (prove)
-- author  : @immiq
-- created : 2026-11-26T13:46:30.452135+00:00
-- url     : https://prove2.me/submissions/77534678-c1f2-4a37-bd66-86e209857e8f

import Mathlib

set_option autoImplicit false

/-- Two prime layers with product at least twice the upper endpoint can meet
in at most one adjacent pair, counting either orientation. -/
theorem solution (p q M x y : ℕ) (hp : p.Prime) (hq : q.Prime) (hne : p ≠ q)
    (hproduct : 2 * M ≤ p * q) (hx : x + 1 ≤ M) (hy : y + 1 ≤ M)
    (hleft : (p ∣ x ∧ q ∣ x + 1) ∨ (q ∣ x ∧ p ∣ x + 1))
    (hright : (p ∣ y ∧ q ∣ y + 1) ∨ (q ∣ y ∧ p ∣ y + 1)) :
    x = y := by
  have hcop := (Nat.coprime_primes hp hq).mpr hne
  have hsame (a b : ℕ) (hcop' : a.Coprime b) (hbig : 2 * M ≤ a * b)
      (hax : a ∣ x) (hay : a ∣ y) (hbx : b ∣ x + 1) (hby : b ∣ y + 1) : x = y := by
    have hdiff (s t : ℕ) (hs : s + 1 ≤ M) (hst : t < s)
        (has : a ∣ s) (hat : a ∣ t) (hbs : b ∣ s + 1) (hbt : b ∣ t + 1) : False := by
      have ha : a ∣ s - t := Nat.dvd_sub has hat
      have hb : b ∣ s - t := by simpa using Nat.dvd_sub hbs hbt
      have hlo := Nat.le_of_dvd (Nat.sub_pos_of_lt hst) (hcop'.mul_dvd_of_dvd_of_dvd ha hb)
      omega
    rcases lt_trichotomy x y with h | h | h
    · exact (hdiff y x hy h hay hax hby hbx).elim
    · exact h
    · exact (hdiff x y hx h hax hay hbx hby).elim
  have hopp (hpx : p ∣ x) (hqx : q ∣ x + 1) (hqy : q ∣ y) (hpy : p ∣ y + 1) : False := by
    have ha : p ∣ x + y + 1 := by simpa only [add_assoc] using dvd_add hpx hpy
    have hb : q ∣ x + y + 1 := by
      have h := dvd_add hqy hqx
      rwa [show y + (x + 1) = x + y + 1 by ac_rfl] at h
    have hlo := Nat.le_of_dvd (by omega : 0 < x + y + 1) (hcop.mul_dvd_of_dvd_of_dvd ha hb)
    omega
  rcases hleft with ⟨hpx, hqx⟩ | ⟨hqx, hpx⟩ <;>
    rcases hright with ⟨hpy, hqy⟩ | ⟨hqy, hpy⟩
  · exact hsame p q hcop hproduct hpx hpy hqx hqy
  · exact (hopp hpx hqx hqy hpy).elim
  · have ha : p ∣ x + y + 1 := by
      have h := dvd_add hpy hpx
      rwa [show y + (x + 1) = x + y + 1 by ac_rfl] at h
    have hb : q ∣ x + y + 1 := by simpa only [add_assoc] using dvd_add hqx hqy
    have hlo := Nat.le_of_dvd (by omega : 0 < x + y + 1) (hcop.mul_dvd_of_dvd_of_dvd ha hb)
    omega
  · exact hsame q p hcop.symm (by simpa only [mul_comm q p] using hproduct) hqx hqy hpx hpy

