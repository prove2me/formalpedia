-- Prove2me | solution 1 for AvramDividend.Classical.avram_gbB281_fourth_power_gaussian_total_good_cell_time_kernel
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-13T22:46:46.18264+00:00
-- url     : https://prove2.me/submissions/570d0bcb-2be8-474b-a768-bf823051e5ad

import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Finset
noncomputable section


private theorem baseKernel (delta : ℝ) :
    ∫ x in (0 : ℝ)..delta, x ^ (-(1 / 2 : ℝ)) =
      2 * Real.sqrt delta := by
  have hr : (-1 : ℝ) < -(1 / 2 : ℝ) := by norm_num
  rw [integral_rpow (a := 0) (b := delta) (r := -(1 / 2 : ℝ)) (Or.inl hr)]
  have hzero : (0 : ℝ) ^ ((-(1 / 2 : ℝ)) + 1) = 0 := by
    norm_num
  rw [hzero]
  norm_num [Real.sqrt_eq_rpow]
  ring


private theorem translatedKernel (s δ : ℝ) :
    ∫ t in s..(s + δ), (t - s) ^ (-(1 / 2 : ℝ)) =
      2 * Real.sqrt δ := by
  rw [intervalIntegral.integral_comp_sub_right
    (fun u : ℝ => u ^ (-(1 / 2 : ℝ))) s]
  simpa only [sub_self, add_sub_cancel_left] using baseKernel δ


private theorem scalingKernel (n m : ℕ) (hm : 0 < m) :
    ((n * m ^ 4 : ℕ) : ℝ) * (1 / ((m : ℝ) ^ 3)) *
      Real.sqrt (1 / ((m : ℝ) ^ 4)) = (n : ℝ) / (m : ℝ) := by
  have hmr : (0 : ℝ) < m := by exact_mod_cast hm
  have hne : (m : ℝ) ≠ 0 := ne_of_gt hmr
  have hsqrt : Real.sqrt (1 / ((m : ℝ) ^ 4)) = 1 / ((m : ℝ) ^ 2) := by
    calc
      Real.sqrt (1 / ((m : ℝ) ^ 4)) =
          Real.sqrt ((1 / ((m : ℝ) ^ 2)) ^ 2) := by
            congr 1
            field_simp <;> ring
      _ = |1 / ((m : ℝ) ^ 2)| := Real.sqrt_sq_eq_abs _
      _ = 1 / ((m : ℝ) ^ 2) := abs_of_pos (by positivity)
  rw [hsqrt]
  push_cast
  field_simp <;> ring


theorem solution (n m : ℕ) (hm : 0 < m) :
    (∑ i ∈ Finset.range (n * m ^ 4),
      (1 / ((m : ℝ) ^ 3)) *
        (∫ t in ((i : ℝ) * (1 / ((m : ℝ) ^ 4)))..
          (((i : ℝ) + 1) * (1 / ((m : ℝ) ^ 4))),
          (t - (i : ℝ) * (1 / ((m : ℝ) ^ 4))) ^ (-(1 / 2 : ℝ)))) =
      2 * (n : ℝ) / (m : ℝ) := by
  let δ : ℝ := 1 / ((m : ℝ) ^ 4)
  let ε : ℝ := 1 / ((m : ℝ) ^ 3)
  have hcell (i : ℕ) :
      (∫ t in ((i : ℝ) * δ)..(((i : ℝ) + 1) * δ),
        (t - (i : ℝ) * δ) ^ (-(1 / 2 : ℝ))) =
        2 * Real.sqrt δ := by
    convert (translatedKernel
      ((i : ℝ) * δ) δ) using 1
    ring
  have hscalar := scalingKernel n m hm
  change (∑ i ∈ Finset.range (n * m ^ 4),
      ε * (∫ t in ((i : ℝ) * δ)..(((i : ℝ) + 1) * δ),
        (t - (i : ℝ) * δ) ^ (-(1 / 2 : ℝ)))) = _
  calc
    _ = ∑ _i ∈ Finset.range (n * m ^ 4), ε * (2 * Real.sqrt δ) := by
      apply Finset.sum_congr rfl
      intro i hi
      rw [hcell i]
    _ = ((n * m ^ 4 : ℕ) : ℝ) * ε * (2 * Real.sqrt δ) := by
      simp [Finset.sum_const, nsmul_eq_mul]
      ring
    _ = 2 * (n : ℝ) / (m : ℝ) := by
      dsimp [ε, δ]
      calc
        _ = 2 * (((n * m ^ 4 : ℕ) : ℝ) * (1 / ((m : ℝ) ^ 3)) *
          Real.sqrt (1 / ((m : ℝ) ^ 4))) := by ring
        _ = _ := by rw [hscalar]; ring
