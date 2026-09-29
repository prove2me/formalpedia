-- Prove2me | solution 1 for BlockCycleRotation.sum_snd_quadruplesQ
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-09-05T11:06:31.546756+00:00
-- url     : https://prove2.me/submissions/b278e7c9-6a00-4f02-9ebe-8241ec1fb109

import Definitions.Def_BlockCycleRotation_Continuant
import Definitions.Def_BlockCycleRotation_Euclid
import Definitions.Def_BlockCycleRotation_ExpSum
import Mathlib

open Real Finset

namespace BlockCycleRotation

@[simp]
theorem remSum_zero (n : ℕ) : remSum n 0 = 0 := by
  rw [remSum]; simp

@[simp]
theorem norm_e (θ : ℝ) : ‖e θ‖ = 1 := Complex.norm_exp_ofReal_mul_I θ

@[simp]
theorem norm_e_pow (θ : ℝ) (n : ℕ) : ‖e θ ^ n‖ = 1 := by
  rw [norm_pow, norm_e, one_pow]

@[simp]
theorem e_zero : e 0 = 1 := by simp [e]

@[simp] theorem K_nil : K [] = 1 := rfl

@[simp] theorem K_singleton (c : ℕ) : K [c] = c := rfl

@[simp] theorem cf_zero (a : ℕ) : cf a 0 = [] := by rw [cf]; simp

/-- The components of a quadruple are bounded by `n`. -/
theorem quadruple_le {n a b a' b' : ℕ} (h1 : 1 ≤ a') (h2 : a' < a) (h3 : 1 ≤ b')
    (h4 : b' < b) (hsum : n = a * b + a' * b') :
    a ≤ n ∧ b ≤ n ∧ a' ≤ n ∧ b' ≤ n := by
  have ha : 1 ≤ a := by omega
  have hb : 1 ≤ b := by omega
  refine ⟨?_, ?_, ?_, ?_⟩ <;> nlinarith

theorem mem_quadruplesAll {n a b a' b' : ℕ} :
    (a, b, a', b') ∈ quadruplesAll n ↔
      (a ≤ n ∧ b ≤ n ∧ a' ≤ n ∧ b' ≤ n) ∧ 1 ≤ a' ∧ a' < a ∧ 1 ≤ b' ∧ b' < b
        ∧ Nat.gcd a a' = 1 ∧ n = a * b + a' * b' := by
  simp [quadruplesAll, Finset.mem_filter, Finset.mem_product, and_assoc]

theorem mem_quadruplesQ {n a b a' b' : ℕ} :
    (a, b, a', b') ∈ quadruplesQ n ↔
      (a ≤ n ∧ b ≤ n ∧ a' ≤ n ∧ b' ≤ n) ∧ 1 ≤ a' ∧ a' < a ∧ 1 ≤ b' ∧ b' < b
        ∧ n = a * b + a' * b' := by
  simp [quadruplesQ, Finset.mem_filter, Finset.mem_product, and_assoc]

end BlockCycleRotation

open BlockCycleRotation in
/-- **`Q(n) = ∑_{d ∣ n} R(n/d)`.**  Classifying quadruples by `d = gcd(a,a')`. -/
theorem solution {n : ℕ} (hn : 0 < n) :
    ∑ q ∈ quadruplesQ n, q.2.1
      = ∑ d ∈ n.divisors, ∑ p ∈ quadruplesAll (n / d), p.2.1:= by
  rw [Finset.sum_sigma']
  refine Finset.sum_bij'
    (i := fun q _ => (⟨Nat.gcd q.1 q.2.2.1,
        (q.1 / Nat.gcd q.1 q.2.2.1, q.2.1, q.2.2.1 / Nat.gcd q.1 q.2.2.1,
          q.2.2.2)⟩ : (_ : ℕ) × (ℕ × ℕ × ℕ × ℕ)))
    (j := fun p _ => (p.1 * p.2.1, p.2.2.1, p.1 * p.2.2.2.1, p.2.2.2.2))
    ?_ ?_ ?_ ?_ ?_
  · rintro ⟨a, b, a', b'⟩ hq
    obtain ⟨-, ha1, ha2, hb1, hb2, hsum⟩ := mem_quadruplesQ.1 hq
    have hd : 0 < Nat.gcd a a' := Nat.gcd_pos_of_pos_left _ (by omega)
    have hda : Nat.gcd a a' ∣ a := Nat.gcd_dvd_left _ _
    have hda' : Nat.gcd a a' ∣ a' := Nat.gcd_dvd_right _ _
    have hdn : Nat.gcd a a' ∣ n := by
      rw [hsum]
      exact Dvd.dvd.add (Dvd.dvd.mul_right hda b) (Dvd.dvd.mul_right hda' b')
    have hnd : n / Nat.gcd a a'
        = a / Nat.gcd a a' * b + a' / Nat.gcd a a' * b' := by
      rw [Nat.div_eq_iff_eq_mul_left hd hdn, hsum, Nat.add_mul, Nat.mul_right_comm,
        Nat.mul_right_comm (a' / Nat.gcd a a'), Nat.div_mul_cancel hda,
        Nat.div_mul_cancel hda']
    have hq1 : 1 ≤ a' / Nat.gcd a a' :=
      (Nat.one_le_div_iff hd).2 (Nat.le_of_dvd (by omega) hda')
    have hq2 : a' / Nat.gcd a a' < a / Nat.gcd a a' :=
      Nat.div_lt_div_of_lt_of_dvd hda ha2
    simp only [Finset.mem_sigma, Nat.mem_divisors]
    exact ⟨⟨hdn, hn.ne'⟩, mem_quadruplesAll.2
      ⟨quadruple_le hq1 hq2 hb1 hb2 hnd, hq1, hq2, hb1, hb2,
        Nat.coprime_div_gcd_div_gcd hd, hnd⟩⟩
  · rintro ⟨d, a1, b, a1', b'⟩ hp
    simp only [Finset.mem_sigma, Nat.mem_divisors] at hp
    obtain ⟨⟨hdn, -⟩, hq⟩ := hp
    obtain ⟨-, ha1, ha2, hb1, hb2, -, hsum⟩ := mem_quadruplesAll.1 hq
    have hd : 0 < d := Nat.pos_of_dvd_of_pos hdn hn
    have hmul : d * (n / d) = n := Nat.mul_div_cancel' hdn
    have hsum' : n = d * a1 * b + d * a1' * b' := by
      rw [← hmul, hsum]; ring
    have hp1 : 1 ≤ d * a1' := Nat.mul_pos hd ha1
    have hp2 : d * a1' < d * a1 := by nlinarith
    rw [mem_quadruplesQ]
    exact ⟨quadruple_le hp1 hp2 hb1 hb2 hsum', hp1, hp2, hb1, hb2, hsum'⟩
  · rintro ⟨a, b, a', b'⟩ hq
    obtain ⟨-, ha1, ha2, -, -, -⟩ := mem_quadruplesQ.1 hq
    have hd : 0 < Nat.gcd a a' := Nat.gcd_pos_of_pos_left _ (by omega)
    have e1 : Nat.gcd a a' * (a / Nat.gcd a a') = a :=
      Nat.mul_div_cancel' (Nat.gcd_dvd_left _ _)
    have e2 : Nat.gcd a a' * (a' / Nat.gcd a a') = a' :=
      Nat.mul_div_cancel' (Nat.gcd_dvd_right _ _)
    rw [e1, e2]
  · rintro ⟨d, a1, b, a1', b'⟩ hp
    simp only [Finset.mem_sigma, Nat.mem_divisors] at hp
    obtain ⟨⟨hdn, -⟩, hq⟩ := hp
    obtain ⟨-, -, -, -, -, hcop, -⟩ := mem_quadruplesAll.1 hq
    have hd : 0 < d := Nat.pos_of_dvd_of_pos hdn hn
    have hgcd : Nat.gcd (d * a1) (d * a1') = d := by
      rw [Nat.gcd_mul_left, hcop, mul_one]
    simp only [hgcd, Nat.mul_div_cancel_left _ hd]
  · rintro ⟨a, b, a', b'⟩ _
    rfl
