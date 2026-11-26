-- Prove2me | solution 1 for Erdos287.odd_affine_tuple_dyadic_size_bound
-- status  : ACCEPTED   (prove)
-- author  : @immiq
-- created : 2026-11-26T12:28:48.52764+00:00
-- url     : https://prove2.me/submissions/ebdc3891-a8b7-4687-a306-afed7f07bf4d

import Mathlib

open Finset

set_option autoImplicit false

private theorem odd_values_preserve_cofactor_parity (c n : ℕ) (hn : Odd n) :
    (c * n) % 2 = c % 2 := by
  rw [Nat.mul_mod, Nat.odd_iff.mp hn, mul_one, Nat.mod_mod]

/-- An admissible tuple with arbitrary affine intercepts still has an
exponential dyadic size bound if every pair gives consecutive multiples. -/
theorem solution (S : Finset (ℕ × ℕ)) (t : ℕ) (hS : S.Nonempty)
    (hodd : ∀ q ∈ S, 0 < q.1 ∧ Odd (q.1 * t + q.2))
    (hpair : ∀ q ∈ S, ∀ r ∈ S, q ≠ r → ∃ c d : ℕ,
      0 < c ∧ 0 < d ∧ c * q.1 = d * r.1 ∧
      (c * (q.1 * t + q.2) + 1 = d * (r.1 * t + r.2) ∨
       d * (r.1 * t + r.2) + 1 = c * (q.1 * t + q.2))) :
    (∀ q ∈ S, ∀ r ∈ S, q ≠ r → padicValNat 2 q.1 ≠ padicValNat 2 r.1) ∧
    ∃ q ∈ S, 2 ^ (S.card - 1) ∣ q.1 := by
  let _ : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hdistinct (q : ℕ × ℕ) (hq : q ∈ S) (r : ℕ × ℕ) (hr : r ∈ S) (hne : q ≠ r) :
      padicValNat 2 q.1 ≠ padicValNat 2 r.1 := by
    obtain ⟨c, d, hc, hd, hlead, hcon⟩ := hpair q hq r hr hne
    have hcmod := odd_values_preserve_cofactor_parity c _ (hodd q hq).2
    have hdmod := odd_values_preserve_cofactor_parity d _ (hodd r hr).2
    have hpar : (2 ∣ c) ↔ ¬ 2 ∣ d := by
      rw [Nat.dvd_iff_mod_eq_zero, Nat.dvd_iff_mod_eq_zero]
      rcases hcon with h | h
      · have hm := congrArg (fun n : ℕ => n % 2) h
        rw [Nat.add_mod, hcmod, hdmod] at hm
        omega
      · have hm := congrArg (fun n : ℕ => n % 2) h
        rw [Nat.add_mod, hcmod, hdmod] at hm
        omega
    have hvc : 2 ∣ c ↔ 1 ≤ padicValNat 2 c := by
      simpa only [pow_one] using (padicValNat_dvd_iff_le (p := 2) (n := 1) hc.ne')
    have hvd : 2 ∣ d ↔ 1 ≤ padicValNat 2 d := by
      simpa only [pow_one] using (padicValNat_dvd_iff_le (p := 2) (n := 1) hd.ne')
    have hl := congrArg (padicValNat 2) hlead
    rw [padicValNat.mul hc.ne' (hodd q hq).1.ne', padicValNat.mul hd.ne' (hodd r hr).1.ne'] at hl
    rw [hvc, hvd] at hpar
    omega
  refine ⟨hdistinct, ?_⟩
  let ν (q : ℕ × ℕ) := padicValNat 2 q.1
  have hinj : Set.InjOn ν (↑S : Set (ℕ × ℕ)) := by
    intro q hq r hr he
    by_contra hn
    exact hdistinct q hq r hr hn he
  by_contra! hno
  have hsub : S.image ν ⊆ range (S.card - 1) := by
    intro e he
    obtain ⟨q, hq, rfl⟩ := mem_image.mp he
    apply mem_range.mpr
    exact lt_of_not_ge fun h => hno q hq ((padicValNat_dvd_iff_le (hodd q hq).1.ne').mpr h)
  have hcard := card_le_card hsub
  rw [card_image_of_injOn hinj, card_range] at hcard
  have hpos := card_pos.mpr hS
  omega

