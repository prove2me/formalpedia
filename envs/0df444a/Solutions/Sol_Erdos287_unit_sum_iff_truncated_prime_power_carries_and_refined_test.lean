-- Prove2me | solution 1 for Erdos287.unit_sum_iff_truncated_prime_power_carries_and_refined_test
-- status  : ACCEPTED   (prove)
-- author  : @immiq
-- created : 2026-11-26T14:42:43.287979+00:00
-- url     : https://prove2.me/submissions/a28a2085-5fb0-4fbc-9c55-e7c546e3326c

import Mathlib
import Theorems.Thm_Erdos287_reciprocal_sum_denominator_cap_iff_top_carries
import Theorems.Thm_Erdos287_reconstruct_unit_sum_at_carry_prime

open Finset

set_option autoImplicit false

/-- Testing the carries above a prime-power threshold and one additional
residue at a chosen prime suffices to reconstruct a unit reciprocal sum. -/
theorem solution (D : Finset ℕ) (L Y p j : ℕ) (hL : 0 < L) (hY : 0 < Y) (hp : p.Prime)
    (hD : ∀ n ∈ D, n ∣ L)
    (hbound : |(∑ n ∈ D, (1 : ℚ) / n) - 1| * (L.gcd (Nat.lcmUpto Y) : ℚ) < (p ^ j : ℕ)) :
    (∑ n ∈ D, (1 : ℚ) / n) = 1 ↔
      (∀ r : ℕ, r.Prime → r ^ (L.factorization r - r.log Y) ∣
        ∑ n ∈ D.filter (fun n => Y < r ^ n.factorization r), L / n) ∧
      p ^ (L.factorization p - p.log Y + j) ∣ Int.natAbs (((∑ n ∈ D, L / n : ℕ) : ℤ) - L) := by
  let W := ∑ n ∈ D, L / n
  let S := ∑ n ∈ D, (1 : ℚ) / n
  let C := Nat.lcmUpto Y
  have hC : 0 < C := Nat.lcmUpto_pos Y
  have hW : (W : ℚ) = (L : ℚ) * S := by
    simp only [W, S, Nat.cast_sum, mul_sum]
    exact sum_congr rfl (fun n hn => by rw [Rat.natCast_div _ _ (hD n hn), mul_one_div])
  have hLQ : (L : ℚ) ≠ 0 := by exact_mod_cast hL.ne'
  have hS : S = (W : ℚ) / L := (eq_div_iff hLQ).mpr (by rw [hW, mul_comm])
  have hk : (L / L.gcd C).factorization p = L.factorization p - p.log Y := by
    simp only [Nat.factorization_div (Nat.gcd_dvd_left L C), Nat.factorization_gcd hL.ne' hC.ne',
      Finsupp.tsub_apply, Finsupp.inf_apply, C, Nat.factorization_lcmUpto Y hp]
    omega
  have htop : S.den ∣ C ↔ ∀ r : ℕ, r.Prime → r ^ (L.factorization r - r.log Y) ∣
      ∑ n ∈ D.filter (fun n => Y < r ^ n.factorization r), L / n := by
    have hi := Erdos287.reciprocal_sum_denominator_cap_iff_top_carries D L C hL hC hD
    rw [hi]
    apply forall_congr'
    intro r
    apply imp_congr_right
    intro hr
    have hrC : C.factorization r = r.log Y := Nat.factorization_lcmUpto Y hr
    have hf : D.filter (fun n => r.log Y < n.factorization r) =
        D.filter (fun n => Y < r ^ n.factorization r) := by
      ext n
      simp only [mem_filter, Nat.log_lt_iff_lt_pow hr.one_lt hY.ne']
    rw [hrC, hf]
  have hbound' : |(W : ℚ) / L - 1| * (L.gcd C : ℚ) < (p ^ j : ℕ) := hS ▸ hbound
  change S = 1 ↔ _ ∧ p ^ (L.factorization p - p.log Y + j) ∣ Int.natAbs ((W : ℤ) - L)
  rw [hS, Erdos287.reconstruct_unit_sum_at_carry_prime W L C p j hL hp hbound', hk, ← hS, htop]

