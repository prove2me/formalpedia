-- Prove2me | solution 1 for AvramDividend.Classical.avram_ga_a219_physical_mesh_gaussian_optimal_positive_chernoff_rate
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-14T01:00:48.741116+00:00
-- url     : https://prove2.me/submissions/6092384e-f1e2-47ae-9ce3-f5327d9dd7c5

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Real Filter Topology AvramDividend.Classical
noncomputable section

theorem solution
    (n m : ℕ) (hn : 0 < n) (θ δ : ℝ) :
    -(δ * ((m : ℝ) + 1) / (2 * (n : ℝ))) * δ +
      ((n : ℝ) / ((m : ℝ) + 1)) *
        (θ + δ * ((m : ℝ) + 1) / (2 * (n : ℝ)))^2 / 2 ≤
      θ * δ / 2 + (n : ℝ) * θ^2 / 2 -
        (3 * δ^2 / (8 * (n : ℝ))) * ((m : ℝ) + 1) := by
  have hnR : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  have hmR : (0 : ℝ) < (m : ℝ) + 1 := by positivity
  have hnm : (n : ℝ) ≠ 0 := ne_of_gt hnR
  have hmm : (m : ℝ) + 1 ≠ 0 := ne_of_gt hmR
  have hprod : 0 ≤ (n : ℝ) * θ^2 :=
    mul_nonneg hnR.le (sq_nonneg _)
  have hfrac : (n : ℝ) * θ^2 / (2 * ((m : ℝ) + 1)) ≤
      (n : ℝ) * θ^2 / 2 := by
    apply div_le_div_of_nonneg_left hprod (by norm_num)
    nlinarith [Nat.cast_nonneg (α := ℝ) m]
  have hEq :
      -(δ * ((m : ℝ) + 1) / (2 * (n : ℝ))) * δ +
        ((n : ℝ) / ((m : ℝ) + 1)) *
          (θ + δ * ((m : ℝ) + 1) / (2 * (n : ℝ)))^2 / 2 =
      θ * δ / 2 + (n : ℝ) * θ^2 / (2 * ((m : ℝ) + 1)) -
        (3 * δ^2 / (8 * (n : ℝ))) * ((m : ℝ) + 1) := by
    field_simp [hnm, hmm]
    ring
  rw [hEq]
  linarith
