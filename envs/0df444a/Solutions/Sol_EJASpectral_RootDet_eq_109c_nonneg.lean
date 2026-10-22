-- Prove2me | solution 1 for EJASpectral.RootDet.eq_109c_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @Ethan Cheung
-- created : 2026-10-21T16:18:22.437193+00:00
-- url     : https://prove2.me/submissions/5c691796-4695-4453-88e7-20dbe638ee8b

import Mathlib

theorem solution {d : ℕ} (hd : 0 < d) (σ : Fin d → ℝ) (φ : ℝ) (hφ : 0 < φ) :
    0 ≤ ((d : ℝ))⁻¹ * φ *
      ∑ i, (σ i - ((d : ℝ))⁻¹ * ∑ j, σ j) ^ 2 *
        (Real.sqrt (∑ j, σ j ^ 2) - ((d : ℝ))⁻¹ * ∑ j, σ j +
          2 * (Real.sqrt (∑ j, σ j ^ 2) - σ i)) := by
  set N := Real.sqrt (∑ j, σ j ^ 2) with hN
  have hle : ∀ i, σ i ≤ N := by
    intro i
    apply Real.le_sqrt_of_sq_le
    exact Finset.single_le_sum (f := fun j => σ j ^ 2) (fun j _ => sq_nonneg _)
      (Finset.mem_univ i)
  have hdpos : (0 : ℝ) < d := by exact_mod_cast hd
  have havg : ((d : ℝ))⁻¹ * ∑ j, σ j ≤ N := by
    rw [inv_mul_le_iff₀ hdpos]
    calc ∑ j, σ j ≤ ∑ _j : Fin d, N := Finset.sum_le_sum (fun j _ => hle j)
      _ = d * N := by simp
  apply mul_nonneg (by positivity)
  apply Finset.sum_nonneg
  intro i _
  apply mul_nonneg (sq_nonneg _)
  linarith [hle i]
