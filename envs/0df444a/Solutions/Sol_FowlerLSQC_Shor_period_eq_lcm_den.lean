-- Prove2me | solution 1 for FowlerLSQC.Shor.period_eq_lcm_den
-- status  : ACCEPTED   (prove)
-- author  : @garyholm
-- created : 2026-11-17T09:33:24.570281+00:00
-- url     : https://prove2.me/submissions/1f039958-eb06-45df-96f0-146161b4ecf0

import Mathlib
namespace FowlerLSQC.Shor

theorem period_eq_lcm_den (r c c' : ℕ) (hc0 : 0 < c) (hcr : c < r) (hc'0 : 0 < c') (hc'r : c' < r)
    (hcop : Nat.Coprime c c') :
    Nat.lcm ((c : ℚ) / r).den ((c' : ℚ) / r).den = r := by
  have hr : 0 < r := by omega
  have den_eq : ∀ x : ℕ, 0 < x → ((x : ℚ) / r).den = r / Nat.gcd x r := by
    intro x hx
    set g := Nat.gcd x r with hg
    have g0 : 0 < g := Nat.gcd_pos_of_pos_left _ hx
    obtain ⟨a, ha⟩ : g ∣ x := Nat.gcd_dvd_left x r
    obtain ⟨b, hb⟩ : g ∣ r := Nat.gcd_dvd_right x r
    have hcop' : Nat.Coprime a b := by
      have := Nat.coprime_div_gcd_div_gcd (m := x) (n := r) g0
      rw [← hg] at this
      have e1 : x / g = a := by rw [ha]; exact Nat.mul_div_cancel_left a g0
      have e2 : r / g = b := by rw [hb]; exact Nat.mul_div_cancel_left b g0
      rwa [e1, e2] at this
    have b0 : 0 < b := by
      rcases Nat.eq_zero_or_pos b with h | h
      · rw [h, mul_zero] at hb; omega
      · exact h
    have hq : (x : ℚ) / r = ((a : ℤ) : ℚ) / ((b : ℤ) : ℚ) := by
      rw [ha, hb]; push_cast
      have : (g : ℚ) ≠ 0 := by exact_mod_cast g0.ne'
      field_simp
    have key := Rat.den_div_eq_of_coprime (a := (a : ℤ)) (b := (b : ℤ)) (by exact_mod_cast b0)
      (by simpa using hcop')
    rw [hq, hb, Nat.mul_div_cancel_left b g0]
    exact_mod_cast key
  rw [den_eq c hc0, den_eq c' hc'0]
  set g := Nat.gcd c r
  set g' := Nat.gcd c' r
  have hgg : Nat.Coprime g g' :=
    (hcop.coprime_dvd_left (Nat.gcd_dvd_left c r)).coprime_dvd_right (Nat.gcd_dvd_left c' r)
  obtain ⟨m, hm⟩ : g * g' ∣ r := hgg.mul_dvd_of_dvd_of_dvd (Nat.gcd_dvd_right c r) (Nat.gcd_dvd_right c' r)
  have g0 : 0 < g := Nat.gcd_pos_of_pos_left _ hc0
  have g0' : 0 < g' := Nat.gcd_pos_of_pos_left _ hc'0
  have e1 : r / g = g' * m := by
    rw [hm, mul_assoc]; exact Nat.mul_div_cancel_left _ g0
  have e2 : r / g' = g * m := by
    rw [hm, mul_comm g g', mul_assoc]; exact Nat.mul_div_cancel_left _ g0'
  rw [e1, e2, Nat.lcm_mul_right, hgg.symm.lcm_eq_mul, hm, mul_comm g' g]

end FowlerLSQC.Shor

theorem solution (r c c' : ℕ) (hc0 : 0 < c) (hcr : c < r) (hc'0 : 0 < c') (hc'r : c' < r)
    (hcop : Nat.Coprime c c') :
    Nat.lcm ((c : ℚ) / r).den ((c' : ℚ) / r).den = r :=
  FowlerLSQC.Shor.period_eq_lcm_den r c c' hc0 hcr hc'0 hc'r hcop
