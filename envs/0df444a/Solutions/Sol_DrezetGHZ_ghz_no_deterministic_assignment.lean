-- Prove2me | solution 1 for DrezetGHZ.ghz_no_deterministic_assignment
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-29T00:38:50.90627+00:00
-- url     : https://prove2.me/submissions/24f486ca-5e82-424b-ae63-83062f8220ab

import Mathlib

theorem solution :
    ¬ ∃ A B : Fin 3 → ℤˣ,
      A 0 * A 1 * A 2 = -1 ∧
      A 0 * B 1 * B 2 = 1 ∧
      B 0 * A 1 * B 2 = 1 ∧
      B 0 * B 1 * A 2 = 1 := by
  rintro ⟨A, B, h1, h2, h3, h4⟩
  have e : (A 0 * A 1 * A 2) * (A 0 * B 1 * B 2) * (B 0 * A 1 * B 2) * (B 0 * B 1 * A 2) =
      (A 0 * A 0) * (A 1 * A 1) * (A 2 * A 2) * (B 0 * B 0) * (B 1 * B 1) * (B 2 * B 2) := by
    simp only [mul_comm, mul_assoc, mul_left_comm]
  rw [h1, h2, h3, h4] at e
  simp only [Int.units_mul_self, mul_one] at e
  have hv := congrArg (fun u : ℤˣ => (u : ℤ)) e
  norm_num at hv
