-- Prove2me | solution 1 for Erdos1210.card_window_small_prime_factor_le
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-26T21:21:00.588772+00:00
-- url     : https://prove2.me/submissions/d7984a56-d7ca-46ce-b8e6-f5c282d78c16

import Mathlib

set_option autoImplicit false

open Finset

theorem solution (n x : ℕ) (A : Finset ℕ)
    (hcop : ∀ a ∈ A, ∀ b ∈ A, a ≠ b → a.Coprime b) :
    ((A.filter (fun a => n - x ≤ a)).filter
        (fun a => ∃ p ≤ x, p.Prime ∧ p ∣ a)).card ≤ Nat.primeCounting x := by
  rw [Nat.primeCounting, Nat.primeCounting', Nat.count_eq_card_filter_range]
  apply Finset.card_le_card_of_injOn Nat.minFac
  · intro a ha
    simp only [Finset.mem_coe, Finset.mem_filter] at ha
    obtain ⟨⟨_, _⟩, p, hpx, hp, hpa⟩ := ha
    have ha1 : a ≠ 1 := by
      rintro rfl
      exact hp.one_lt.ne' (Nat.dvd_one.mp hpa)
    simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_range]
    refine ⟨?_, Nat.minFac_prime ha1⟩
    have := Nat.minFac_le_of_dvd hp.two_le hpa
    omega
  · intro a ha b hb hab
    simp only [Finset.mem_coe, Finset.mem_filter] at ha hb
    obtain ⟨⟨haA, _⟩, p, _, hp, hpa⟩ := ha
    obtain ⟨⟨hbA, _⟩, q, _, hq, hqb⟩ := hb
    by_contra hne
    have ha1 : a ≠ 1 := by
      rintro rfl
      exact hp.one_lt.ne' (Nat.dvd_one.mp hpa)
    have hcp := hcop a haA b hbA hne
    have h1 : a.minFac ∣ a := Nat.minFac_dvd a
    have h2 : a.minFac ∣ b := hab ▸ Nat.minFac_dvd b
    have h3 : a.minFac ∣ Nat.gcd a b := Nat.dvd_gcd h1 h2
    rw [hcp] at h3
    exact (Nat.minFac_prime ha1).one_lt.ne' (Nat.dvd_one.mp h3)
