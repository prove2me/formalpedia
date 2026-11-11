-- Prove2me | solution 1 for AvramDividend.Classical.avram_gledger59_clipped_finite_source_one_sided_upper_sum
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-11T00:34:06.344431+00:00
-- url     : https://prove2.me/submissions/e0c9a632-282f-406f-a7a5-984ed8c00ddb

import Mathlib
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

noncomputable section

/-- A clipped source cell either vanishes or is bounded using a lower
    compact-state value bound and a one-sided upper terminal envelope. -/
theorem solution
    (m : ℕ) (E Y Z : ℕ → ℝ) (w : ℝ → ℝ) (θ K b : ℝ)
    (hK : 0 ≤ K) (hb : 0 ≤ b)
    (hE0 : ∀ i, 0 ≤ E i) (hE1 : ∀ i, E i ≤ 1)
    (hcell : ∀ i ∈ Finset.range (m + 1),
      (E (i + 1) = E i ∧ Z i = Y i) ∨
      (-b ≤ w (Y i) ∧ w (Z i) ≤ K * Real.exp (θ * Z i))) :
    (Finset.sum (Finset.range (m + 1)) (fun i =>
      (E (i + 1) - E i) * w (Y i) +
        E (i + 1) * (w (Z i) - w (Y i)))) ≤
    (Finset.sum (Finset.range (m + 1)) (fun i =>
      K * Real.exp (θ * Z i) + b)) := by
  apply Finset.sum_le_sum
  intro i hi
  rcases hcell i hi with ⟨hEq, hZ⟩ | ⟨hY, hZ⟩
  · have hzero :
        (E (i + 1) - E i) * w (Y i) +
          E (i + 1) * (w (Z i) - w (Y i)) = 0 := by
      rw [hEq, hZ]
      ring
    rw [hzero]
    exact add_nonneg (mul_nonneg hK (Real.exp_pos _).le) hb
  · have hExp : 0 ≤ K * Real.exp (θ * Z i) :=
      mul_nonneg hK (Real.exp_pos _).le
    have hTop : E (i + 1) * w (Z i) ≤
        E (i + 1) * (K * Real.exp (θ * Z i)) :=
      mul_le_mul_of_nonneg_left hZ (hE0 _)
    have hEtop : E (i + 1) * (K * Real.exp (θ * Z i)) ≤
        K * Real.exp (θ * Z i) := by
      nlinarith [mul_nonneg (sub_nonneg.mpr (hE1 (i + 1))) hExp]
    have hBottom : -(E i * w (Y i)) ≤ E i * b := by
      nlinarith [mul_le_mul_of_nonneg_left hY (hE0 i)]
    have hEbottom : E i * b ≤ b := by
      nlinarith [mul_nonneg (sub_nonneg.mpr (hE1 i)) hb]
    calc
      (E (i + 1) - E i) * w (Y i) +
          E (i + 1) * (w (Z i) - w (Y i)) =
        E (i + 1) * w (Z i) - E i * w (Y i) := by ring
      _ ≤ K * Real.exp (θ * Z i) + b := by linarith
