-- Prove2me | solution 1 for Erdos287.reconstruct_unit_sum_at_carry_prime
-- status  : ACCEPTED   (prove)
-- author  : @immiq
-- created : 2026-11-26T14:41:13.977254+00:00
-- url     : https://prove2.me/submissions/3f435df2-1034-4488-9986-2115bf20b50c

import Mathlib
import Theorems.Thm_Erdos287_cleared_denominator_cap_iff
import Theorems.Thm_Erdos287_reconstruct_unit_sum_from_residual_numerator

set_option autoImplicit false

/-- The final residual congruence can be checked by increasing the precision
at a prime already used to test the denominator cap. -/
theorem solution (W L C p j : ℕ) (hL : 0 < L) (hp : p.Prime)
    (hbound : |(W : ℚ) / L - 1| * (L.gcd C : ℚ) < (p ^ j : ℕ)) :
    (W : ℚ) / L = 1 ↔
      ((W : ℚ) / L).den ∣ C ∧
        p ^ ((L / L.gcd C).factorization p + j) ∣ Int.natAbs ((W : ℤ) - L) := by
  let G := L.gcd C
  let K := L / G
  let U := W / K
  let E := ((U : ℤ) - G).natAbs
  have hG : 0 < G := Nat.gcd_pos_of_pos_left C hL
  have hK : 0 < K := Nat.div_pos (Nat.le_of_dvd hL (Nat.gcd_dvd_left L C)) hG
  have hKG : K * G = L := Nat.div_mul_cancel (Nat.gcd_dvd_left L C)
  have hreconstruct := Erdos287.reconstruct_unit_sum_from_residual_numerator W L C (p ^ j) hL hbound
  rw [hreconstruct]
  change ((W : ℚ) / L).den ∣ C ∧ U ≡ G [MOD p ^ j] ↔
    ((W : ℚ) / L).den ∣ C ∧ p ^ (K.factorization p + j) ∣ Int.natAbs ((W : ℤ) - L)
  refine and_congr_right fun hcap => ?_
  have hKW : K ∣ W := (Erdos287.cleared_denominator_cap_iff W L C hL).mp hcap
  have hKU : K * U = W := Nat.mul_div_cancel' hKW
  have hE : ((W : ℤ) - L).natAbs = K * E := by
    have he : (W : ℤ) - L = (K : ℤ) * ((U : ℤ) - G) := by
      rw [mul_sub, ← Int.natCast_mul, ← Int.natCast_mul, hKU, hKG]
    rw [he, Int.natAbs_mul, Int.natAbs_natCast]
  have hmod : U ≡ G [MOD p ^ j] ↔ p ^ j ∣ E := by
    rw [Nat.ModEq.comm, Nat.modEq_iff_dvd]
    simpa only [E, Int.natAbs_natCast] using
      (Int.natAbs_dvd_natAbs (a := ((p ^ j : ℕ) : ℤ)) (b := (U : ℤ) - G)).symm
  rw [hmod, hE]
  by_cases hzero : E = 0
  · simp [hzero]
  · rw [hp.pow_dvd_iff_le_factorization hzero,
      hp.pow_dvd_iff_le_factorization (mul_ne_zero hK.ne' hzero),
      Nat.factorization_mul hK.ne' hzero, Finsupp.add_apply]
    omega

