-- Prove2me | solution 1 for Erdos1210.minfac_injective_of_pairwise_coprime
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-30T17:01:55.541238+00:00
-- url     : https://prove2.me/submissions/facc81aa-0bcb-42a7-8bac-b551fa789e40

import Mathlib

theorem solution :
    ∀ A : Finset ℕ,
      (∀ a ∈ A, ∀ b ∈ A, a ≠ b → a.Coprime b) →
      Set.InjOn (fun a => a.minFac) {a ∈ (↑A : Set ℕ) | 2 ≤ a} := by
  intro A h a ha b hb he
  by_contra hn
  have hc := h a ha.1 b hb.1 hn
  have hd : a.minFac ∣ Nat.gcd a b := Nat.dvd_gcd (Nat.minFac_dvd a) (by simpa only [he] using Nat.minFac_dvd b)
  rw [hc.gcd_eq_one] at hd
  have hp := Nat.minFac_prime (show a ≠ 1 by have := ha.2; omega)
  exact hp.not_dvd_one hd
