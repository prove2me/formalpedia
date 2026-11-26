-- Prove2me | solution 1 for Erdos287.large_prime_removes_exceptional_conductor
-- status  : ACCEPTED   (prove)
-- author  : @immiq
-- created : 2026-11-26T20:14:30.547951+00:00
-- url     : https://prove2.me/submissions/5ac71cad-1661-4f57-b1c2-e7380c652567

import Mathlib

open Finset

set_option autoImplicit false

/-- An exceptional conductor with a bounded part and a squarefree part
has a prime above the presieve cutoff once it exceeds the primorial bound. -/
theorem solution (r d b w : ℕ) (hs : Squarefree d)
    (hr : r ∣ b * d) (hd : d ∣ r) (hb : 0 < b) (hlarge : b * 4 ^ w < r) :
    ∃ p : ℕ, p.Prime ∧ w < p ∧ p ∣ r ∧
      (∀ (ι : Type) (T : Finset ι) (m : ι → ℕ),
        (∀ i ∈ T, ¬ p ∣ m i) → ¬ r ∣ ∏ i ∈ T, m i) ∧
      (∀ K ν η : ℝ, 0 ≤ η → η ≤ ν → ν ≤ K → 2 * K < p →
        0 ≤ ((p : ℝ) - η) / ((p : ℝ) - ν) - 1 ∧
        ((p : ℝ) - η) / ((p : ℝ) - ν) - 1 ≤ 2 * K / p) := by
  have hbig : ∃ p ∈ d.primeFactors, w < p := by
    by_contra! h
    have hsub : d.primeFactors ⊆ (range (w + 1)).filter Nat.Prime := by
      intro p hp
      exact mem_filter.mpr ⟨mem_range.mpr (Nat.lt_succ_of_le (h p hp)),
        (Nat.mem_primeFactors.mp hp).1⟩
    have hdiv : d ∣ primorial w := by
      rw [← Nat.prod_primeFactors_of_squarefree hs, primorial]
      exact prod_dvd_prod_of_subset _ _ _ hsub
    have hbound : d ≤ 4 ^ w := (Nat.le_of_dvd (primorial_pos w) hdiv).trans
      (primorial_le_four_pow w)
    have hpos : 0 < d := Nat.pos_of_ne_zero hs.ne_zero
    exact hlarge.not_ge ((Nat.le_of_dvd (Nat.mul_pos hb hpos) hr).trans
      (Nat.mul_le_mul_left b hbound))
  obtain ⟨p, hp, hw⟩ := hbig
  obtain ⟨hpp, hpd, _⟩ := Nat.mem_primeFactors.mp hp
  have hpr : p ∣ r := hpd.trans hd
  refine ⟨p, hpp, hw, hpr, ?_, ?_⟩
  · intro ι T m havoid hprod
    obtain ⟨i, hi, hpi⟩ := (hpp.prime.dvd_finsetProd_iff _).mp (hpr.trans hprod)
    exact havoid i hi hpi
  · intro K ν η hη hην hνK hKp
    have hK : 0 ≤ K := hη.trans (hην.trans hνK)
    have hp0 : (0 : ℝ) < p := by linarith
    have hden : 0 < (p : ℝ) - ν := by linarith
    have hratio : ((p : ℝ) - η) / ((p : ℝ) - ν) - 1 =
        (ν - η) / ((p : ℝ) - ν) := by
      field_simp
      ring
    rw [hratio]
    refine ⟨div_nonneg (sub_nonneg.mpr hην) hden.le, ?_⟩
    calc
      _ ≤ K / ((p : ℝ) - ν) := div_le_div_of_nonneg_right (by linarith) hden.le
      _ ≤ K / ((p : ℝ) / 2) := div_le_div_of_nonneg_left hK (by positivity) (by linarith)
      _ = _ := by ring

