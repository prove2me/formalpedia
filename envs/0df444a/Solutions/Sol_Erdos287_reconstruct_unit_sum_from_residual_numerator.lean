-- Prove2me | solution 1 for Erdos287.reconstruct_unit_sum_from_residual_numerator
-- status  : ACCEPTED   (prove)
-- author  : @immiq
-- created : 2026-11-26T14:39:08.579231+00:00
-- url     : https://prove2.me/submissions/cfd01c47-1415-477f-9698-8fafd1cdafa6

import Mathlib
import Theorems.Thm_Erdos287_cleared_denominator_cap_iff

set_option autoImplicit false

/-- After the denominator cap is verified, a further residue test needs only
the error scaled by the surviving denominator. -/
theorem solution (W L C q : ℕ) (hL : 0 < L)
    (hbound : |(W : ℚ) / L - 1| * (L.gcd C : ℚ) < q) :
    (W : ℚ) / L = 1 ↔
      ((W : ℚ) / L).den ∣ C ∧ W / (L / L.gcd C) ≡ L.gcd C [MOD q] := by
  let G := L.gcd C
  let K := L / G
  have hG : 0 < G := Nat.gcd_pos_of_pos_left C hL
  have hK : 0 < K := Nat.div_pos (Nat.le_of_dvd hL (Nat.gcd_dvd_left L C)) hG
  have hKG : K * G = L := Nat.div_mul_cancel (Nat.gcd_dvd_left L C)
  have hGQ : (G : ℚ) ≠ 0 := by exact_mod_cast hG.ne'
  have hLQ : (L : ℚ) ≠ 0 := by exact_mod_cast hL.ne'
  change (W : ℚ) / L = 1 ↔ ((W : ℚ) / L).den ∣ C ∧ W / K ≡ G [MOD q]
  constructor
  · intro h
    have hWL : W = L := by exact_mod_cast ((div_eq_iff hLQ).mp h).trans (one_mul _)
    refine ⟨by simp [h], ?_⟩
    have hLG : L / K = G := calc
      L / K = (G * K) / K := by rw [mul_comm G K, hKG]
      _ = G := Nat.mul_div_cancel G hK
    rw [hWL, hLG]
  · rintro ⟨hcap, htest⟩
    have hdiv : K ∣ W := (Erdos287.cleared_denominator_cap_iff W L C hL).mp hcap
    let U := W / K
    have hUK : U * K = W := Nat.div_mul_cancel hdiv
    have hfraction : (W : ℚ) / L = (U : ℚ) / G := by
      apply (div_eq_div_iff hLQ hGQ).mpr
      exact_mod_cast (show W * G = U * L by rw [← hUK, mul_assoc, hKG])
    have he (u : ℚ) : (u / (G : ℚ) - 1) * G = u - G := by
      rw [sub_mul, div_mul_cancel₀ u hGQ, one_mul]
    let E : ℤ := (U : ℤ) - G
    have hsmall : E.natAbs < q := by
      have hq : (0 : ℚ) ≤ (G : ℚ) := by positivity
      have hreal : |(U : ℚ) - G| < q := calc
        _ = |((U : ℚ) / G - 1) * G| := by rw [he]
        _ = |(U : ℚ) / G - 1| * G := by rw [abs_mul, abs_of_nonneg hq]
        _ < _ := hfraction ▸ hbound
      have hcast : (E.natAbs : ℚ) = |(U : ℚ) - G| := by
        calc
          _ = ((E.natAbs : ℤ) : ℚ) := (Int.cast_natCast E.natAbs).symm
          _ = |(E : ℚ)| := by rw [Int.natCast_natAbs, Int.cast_abs]
          _ = _ := by simp [E]
      exact_mod_cast (show (E.natAbs : ℚ) < q by rwa [hcast])
    have hEdvd : (q : ℤ) ∣ E := Nat.modEq_iff_dvd.mp htest.symm
    have hzero : E = 0 := by
      by_contra hne
      have hqE : q ∣ E.natAbs := by simpa using Int.natAbs_dvd_natAbs.mpr hEdvd
      exact hsmall.not_ge (Nat.le_of_dvd (Int.natAbs_pos.mpr hne) hqE)
    have hUG : U = G := by
      change (U : ℤ) - G = 0 at hzero
      exact_mod_cast sub_eq_zero.mp hzero
    rw [hfraction, hUG, div_self hGQ]

