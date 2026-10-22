-- Prove2me | solution 1 for FastCLO.LowerBound.posterior_identity
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T16:30:32.417493+00:00
-- url     : https://prove2.me/submissions/85a9a4cd-d865-4b41-8bd5-598ca3c28c30

import Mathlib
set_option autoImplicit false

theorem pp_a_aux (ζ : ℝ) (h0 : 0 ≤ ζ) (h1 : ζ < 1) (N d : ℕ) :
    min (((1 + ζ) / 2) ^ (N + d) * ((1 - ζ) / 2) ^ N) (((1 + ζ) / 2) ^ N * ((1 - ζ) / 2) ^ (N + d)) /
        (((1 + ζ) / 2) ^ (N + d) * ((1 - ζ) / 2) ^ N + ((1 + ζ) / 2) ^ N * ((1 - ζ) / 2) ^ (N + d)) =
      1 / (1 + ((1 + ζ) / (1 - ζ)) ^ d) := by
  set a := (1 + ζ) / 2 with ha
  set c := (1 - ζ) / 2 with hc
  have hcpos : 0 < c := by rw [hc]; linarith
  have hapos : 0 < a := by rw [ha]; linarith
  have hca : c ≤ a := by rw [ha, hc]; linarith
  have hr : (1 + ζ) / (1 - ζ) = a / c := by rw [ha, hc]; field_simp
  rw [hr]
  have hP : 0 < a ^ N * c ^ N := by positivity
  have hcd : c ^ d ≤ a ^ d := pow_le_pow_left₀ hcpos.le hca d
  have e1 : a ^ (N + d) * c ^ N = (a ^ N * c ^ N) * a ^ d := by ring
  have e2 : a ^ N * c ^ (N + d) = (a ^ N * c ^ N) * c ^ d := by ring
  rw [e1, e2]
  have hm : min ((a ^ N * c ^ N) * a ^ d) ((a ^ N * c ^ N) * c ^ d) = (a ^ N * c ^ N) * c ^ d :=
    min_eq_right (mul_le_mul_of_nonneg_left hcd hP.le)
  rw [hm]
  have hdp : (a / c) ^ d = a ^ d / c ^ d := div_pow _ _ _
  rw [hdp]
  have hcd0 : 0 < c ^ d := by positivity
  have had0 : 0 < a ^ d := by positivity
  field_simp
  ring

theorem solution (ζ : ℝ) (h0 : 0 ≤ ζ) (h1 : ζ < 1) (N0 N1 : ℕ) :
    min (((1 + ζ) / 2) ^ N1 * ((1 - ζ) / 2) ^ N0) (((1 + ζ) / 2) ^ N0 * ((1 - ζ) / 2) ^ N1) /
        (((1 + ζ) / 2) ^ N1 * ((1 - ζ) / 2) ^ N0 + ((1 + ζ) / 2) ^ N0 * ((1 - ζ) / 2) ^ N1) =
      1 / (1 + ((1 + ζ) / (1 - ζ)) ^ (Int.natAbs ((N1 : ℤ) - N0))) := by
  rcases le_total N0 N1 with h | h
  · obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le h
    have : Int.natAbs (((N0 + d : ℕ) : ℤ) - N0) = d := by
      push_cast; simp
    rw [this]
    exact pp_a_aux ζ h0 h1 N0 d
  · obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le h
    have : Int.natAbs ((N1 : ℤ) - ((N1 + d : ℕ) : ℤ)) = d := by
      push_cast; simp
    rw [this, min_comm, ← pp_a_aux ζ h0 h1 N1 d, add_comm (((1 + ζ) / 2) ^ (N1 + d) * ((1 - ζ) / 2) ^ N1)]
