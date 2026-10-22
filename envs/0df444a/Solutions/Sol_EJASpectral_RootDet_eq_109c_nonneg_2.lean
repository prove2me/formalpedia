-- Prove2me | solution 2 for EJASpectral.RootDet.eq_109c_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T16:37:24.186136+00:00
-- url     : https://prove2.me/submissions/2bd3030e-3d16-4075-a545-5f1dea05a513

import Mathlib
set_option autoImplicit false

theorem solution {d : ℕ} (hd : 0 < d) (σ : Fin d → ℝ) (φ : ℝ) (hφ : 0 < φ) :
    0 ≤ ((d : ℝ))⁻¹ * φ *
      ∑ i, (σ i - ((d : ℝ))⁻¹ * ∑ j, σ j) ^ 2 *
        (Real.sqrt (∑ j, σ j ^ 2) - ((d : ℝ))⁻¹ * ∑ j, σ j +
          2 * (Real.sqrt (∑ j, σ j ^ 2) - σ i)) := by
  have hle : ∀ i, σ i ≤ Real.sqrt (∑ j, σ j ^ 2) := fun i => by
    have h : σ i ^ 2 ≤ ∑ j, σ j ^ 2 :=
      Finset.single_le_sum (f := fun j => σ j ^ 2) (fun j _ => sq_nonneg _) (Finset.mem_univ i)
    exact (le_abs_self _).trans (Real.abs_le_sqrt h)
  have hdpos : (0 : ℝ) < d := by exact_mod_cast hd
  have hm : ((d : ℝ))⁻¹ * ∑ j, σ j ≤ Real.sqrt (∑ j, σ j ^ 2) := by
    have h1 : ∑ j, σ j ≤ d * Real.sqrt (∑ j, σ j ^ 2) := by
      calc ∑ j, σ j ≤ ∑ _j : Fin d, Real.sqrt (∑ j, σ j ^ 2) := Finset.sum_le_sum (fun j _ => hle j)
        _ = d * Real.sqrt (∑ j, σ j ^ 2) := by simp
    calc ((d : ℝ))⁻¹ * ∑ j, σ j ≤ ((d : ℝ))⁻¹ * (d * Real.sqrt (∑ j, σ j ^ 2)) := by gcongr
      _ = Real.sqrt (∑ j, σ j ^ 2) := by field_simp
  apply mul_nonneg (by positivity)
  apply Finset.sum_nonneg
  intro i _
  apply mul_nonneg (sq_nonneg _)
  linarith [hle i, hm]
