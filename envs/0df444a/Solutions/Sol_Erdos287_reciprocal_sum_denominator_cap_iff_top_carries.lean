-- Prove2me | solution 1 for Erdos287.reciprocal_sum_denominator_cap_iff_top_carries
-- status  : ACCEPTED   (prove)
-- author  : @immiq
-- created : 2026-11-26T14:38:55.427546+00:00
-- url     : https://prove2.me/submissions/99b68e63-b94c-4838-b275-0eed77ae97c4

import Mathlib
import Theorems.Thm_Erdos287_cleared_denominator_cap_iff

open Finset

set_option autoImplicit false

/-- One congruence per prime controls the reduced denominator of a reciprocal
sum. Terms at or below the cap's valuation vanish from that congruence. -/
theorem solution (D : Finset ℕ) (L C : ℕ) (hL : 0 < L) (hC : 0 < C)
    (hD : ∀ n ∈ D, n ∣ L) :
    (∑ n ∈ D, (1 : ℚ) / n).den ∣ C ↔
      ∀ p : ℕ, p.Prime →
        p ^ (L.factorization p - C.factorization p) ∣
          ∑ n ∈ D.filter (fun n => C.factorization p < n.factorization p), L / n := by
  let W := ∑ n ∈ D, L / n
  let S := ∑ n ∈ D, (1 : ℚ) / n
  let K := L / L.gcd C
  have hK : 0 < K := Nat.div_pos (Nat.le_of_dvd hL (Nat.gcd_dvd_left L C))
    (Nat.gcd_pos_of_pos_left C hL)
  have hW : (W : ℚ) = (L : ℚ) * S := by
    simp only [W, S, Nat.cast_sum, mul_sum]
    apply sum_congr rfl
    intro n hn
    rw [Rat.natCast_div _ _ (hD n hn), mul_one_div]
  have hLQ : (L : ℚ) ≠ 0 := by exact_mod_cast hL.ne'
  have hS : S = (W : ℚ) / L := (eq_div_iff hLQ).mpr (by rw [hW, mul_comm])
  change S.den ∣ C ↔ _
  rw [hS, Erdos287.cleared_denominator_cap_iff W L C hL]
  have hKfactor (p : ℕ) : K.factorization p = L.factorization p - C.factorization p := by
    simp only [K, Nat.factorization_div (Nat.gcd_dvd_left L C),
      Nat.factorization_gcd hL.ne' hC.ne', Finsupp.tsub_apply, Finsupp.inf_apply]
    omega
  have hpartial (p : ℕ) (hp : p.Prime) :
      p ^ K.factorization p ∣ W ↔
        p ^ K.factorization p ∣
          ∑ n ∈ D.filter (fun n => C.factorization p < n.factorization p), L / n := by
    let high := D.filter (fun n => C.factorization p < n.factorization p)
    let low := D.filter (fun n => ¬ C.factorization p < n.factorization p)
    have hsplit : (∑ n ∈ high, L / n) + (∑ n ∈ low, L / n) = W :=
      sum_filter_add_sum_filter_not D (fun n => C.factorization p < n.factorization p) _
    have hlow : p ^ K.factorization p ∣ ∑ n ∈ low, L / n := by
      apply dvd_sum
      intro n hn
      obtain ⟨hnD, hnle⟩ := mem_filter.mp hn
      have hdiv := Nat.div_mul_cancel (hD n hnD)
      have hpos : L / n ≠ 0 := by
        intro hz
        rw [hz, zero_mul] at hdiv
        exact hL.ne' hdiv.symm
      apply (hp.pow_dvd_iff_le_factorization hpos).mpr
      rw [hKfactor, Nat.factorization_div (hD n hnD), Finsupp.tsub_apply]
      exact Nat.sub_le_sub_left (le_of_not_gt hnle) _
    rw [← hsplit]
    exact (Nat.dvd_add_iff_left hlow).symm
  constructor
  · intro h p hp
    rw [← hKfactor]
    exact (hpartial p hp).mp ((hp.pow_dvd_iff_le_factorization hK.ne').mpr le_rfl |>.trans h)
  · intro h
    change K ∣ W
    by_cases hz : W = 0
    · simp [hz]
    · apply (Nat.factorization_le_iff_dvd hK.ne' hz).mp
      intro p
      by_cases hp : p.Prime
      · apply (hp.pow_dvd_iff_le_factorization hz).mp
        apply (hpartial p hp).mpr
        rw [hKfactor]
        exact h p hp
      · simp [Nat.factorization_eq_zero_of_not_prime K hp]

