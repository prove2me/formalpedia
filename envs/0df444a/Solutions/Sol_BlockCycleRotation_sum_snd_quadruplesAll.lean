-- Prove2me | solution 1 for BlockCycleRotation.sum_snd_quadruplesAll
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-09-05T11:06:11.859105+00:00
-- url     : https://prove2.me/submissions/45f38a00-3484-4bc0-878d-a5fe0004ff23

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

theorem mem_quadruples {n a b a' b' : ℕ} :
    (a, b, a', b') ∈ quadruples n ↔
      (a ≤ n ∧ b ≤ n ∧ a' ≤ n ∧ b' ≤ n) ∧ 1 ≤ a' ∧ a' < a ∧ 1 ≤ b' ∧ b' < b
        ∧ Nat.gcd a a' = 1 ∧ Nat.gcd b b' = 1 ∧ n = a * b + a' * b' := by
  simp [quadruples, Finset.mem_filter, Finset.mem_product, and_assoc]

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

end BlockCycleRotation

open BlockCycleRotation in
/-- **Classifying the quadruples by `gcd(b,b')`.** -/
theorem solution {n : ℕ} (hn : 0 < n) :
    ∑ q ∈ quadruplesAll n, q.2.1
      = ∑ e ∈ n.divisors, e * ∑ p ∈ quadruples (n / e), p.2.1:= by
  rw [show (∑ e ∈ n.divisors, e * ∑ p ∈ quadruples (n / e), p.2.1)
      = ∑ e ∈ n.divisors, ∑ p ∈ quadruples (n / e), e * p.2.1 from
    Finset.sum_congr rfl fun e _ => Finset.mul_sum _ _ _, Finset.sum_sigma']
  refine Finset.sum_bij'
    (i := fun q _ => (⟨Nat.gcd q.2.1 q.2.2.2,
        (q.1, q.2.1 / Nat.gcd q.2.1 q.2.2.2, q.2.2.1,
          q.2.2.2 / Nat.gcd q.2.1 q.2.2.2)⟩ : (_ : ℕ) × (ℕ × ℕ × ℕ × ℕ)))
    (j := fun p _ => (p.2.1, p.1 * p.2.2.1, p.2.2.2.1, p.1 * p.2.2.2.2))
    ?_ ?_ ?_ ?_ ?_
  · -- forward
    rintro ⟨a, b, a', b'⟩ hq
    obtain ⟨⟨-, -, -, -⟩, ha1, ha2, hb1, hb2, hga, hsum⟩ := mem_quadruplesAll.1 hq
    have he : 0 < Nat.gcd b b' := Nat.gcd_pos_of_pos_left _ (by omega)
    have heb : Nat.gcd b b' ∣ b := Nat.gcd_dvd_left _ _
    have heb' : Nat.gcd b b' ∣ b' := Nat.gcd_dvd_right _ _
    have hen : Nat.gcd b b' ∣ n := by
      rw [hsum]
      exact Dvd.dvd.add (Dvd.dvd.mul_left heb a) (Dvd.dvd.mul_left heb' a')
    have hne : n / Nat.gcd b b' = a * (b / Nat.gcd b b') + a' * (b' / Nat.gcd b b') := by
      rw [Nat.div_eq_iff_eq_mul_left he hen, hsum, Nat.add_mul, Nat.mul_assoc,
        Nat.mul_assoc, Nat.div_mul_cancel heb, Nat.div_mul_cancel heb']
    simp only [Finset.mem_sigma, Nat.mem_divisors]
    refine ⟨⟨hen, hn.ne'⟩, mem_quadruples.2 ⟨?_, ha1, ha2, ?_, ?_, hga, ?_, hne⟩⟩
    · refine quadruple_le ha1 ha2 ?_ ?_ hne
      · exact (Nat.one_le_div_iff he).2 (Nat.le_of_dvd (by omega) heb')
      · exact Nat.div_lt_div_of_lt_of_dvd heb hb2
    · exact (Nat.one_le_div_iff he).2 (Nat.le_of_dvd (by omega) heb')
    · exact Nat.div_lt_div_of_lt_of_dvd heb hb2
    · exact Nat.coprime_div_gcd_div_gcd he
  · -- backward
    rintro ⟨e, a, b1, a', b1'⟩ hp
    simp only [Finset.mem_sigma, Nat.mem_divisors] at hp
    obtain ⟨⟨hen, -⟩, hq⟩ := hp
    obtain ⟨-, ha1, ha2, hb1, hb2, hga, -, hsum⟩ := mem_quadruples.1 hq
    have he : 0 < e := Nat.pos_of_dvd_of_pos hen hn
    have hmul : e * (n / e) = n := Nat.mul_div_cancel' hen
    have hsum' : n = a * (e * b1) + a' * (e * b1') := by
      rw [← hmul, hsum]; ring
    rw [mem_quadruplesAll]
    have hp1 : 1 ≤ e * b1' := Nat.mul_pos he hb1
    have hp2 : e * b1' < e * b1 := by nlinarith
    exact ⟨quadruple_le ha1 ha2 hp1 hp2 hsum', ha1, ha2, hp1, hp2, hga, hsum'⟩
  · -- left inverse
    rintro ⟨a, b, a', b'⟩ hq
    obtain ⟨-, -, -, hb1, hb2, -, -⟩ := mem_quadruplesAll.1 hq
    have he : 0 < Nat.gcd b b' := Nat.gcd_pos_of_pos_left _ (by omega)
    have e1 : Nat.gcd b b' * (b / Nat.gcd b b') = b :=
      Nat.mul_div_cancel' (Nat.gcd_dvd_left _ _)
    have e2 : Nat.gcd b b' * (b' / Nat.gcd b b') = b' :=
      Nat.mul_div_cancel' (Nat.gcd_dvd_right _ _)
    rw [e1, e2]
  · -- right inverse
    rintro ⟨e, a, b1, a', b1'⟩ hp
    simp only [Finset.mem_sigma, Nat.mem_divisors] at hp
    obtain ⟨⟨hen, -⟩, hq⟩ := hp
    obtain ⟨-, -, -, hb1, hb2, -, hcop, -⟩ := mem_quadruples.1 hq
    have he : 0 < e := Nat.pos_of_dvd_of_pos hen hn
    have hgcd : Nat.gcd (e * b1) (e * b1') = e := by
      rw [Nat.gcd_mul_left, hcop, mul_one]
    simp only [hgcd, Nat.mul_div_cancel_left _ he]
  · rintro ⟨a, b, a', b'⟩ hq
    obtain ⟨-, -, -, hb1, hb2, -, -⟩ := mem_quadruplesAll.1 hq
    have he : 0 < Nat.gcd b b' := Nat.gcd_pos_of_pos_left _ (by omega)
    exact (Nat.mul_div_cancel' (Nat.gcd_dvd_left b b')).symm
