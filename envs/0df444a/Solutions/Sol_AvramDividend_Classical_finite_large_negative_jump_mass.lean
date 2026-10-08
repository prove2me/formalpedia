-- Prove2me | solution 1 for AvramDividend.Classical.finite_large_negative_jump_mass
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-06T11:44:55.677118+00:00
-- url     : https://prove2.me/submissions/12a844c0-786c-40ef-8b72-cc4aa0b8650e

import Mathlib

open MeasureTheory Set
open scoped ENNReal

theorem solution
    (ν : Measure ℝ)
    (hν : (∫⁻ y : ℝ, ENNReal.ofReal (min (1 : ℝ) (y ^ 2)) ∂ν) < ⊤) :
    ν (Iic (-1 : ℝ)) ≠ ⊤ := by
  have hpoint : ∀ y : ℝ,
      (Iic (-1 : ℝ)).indicator (fun _ : ℝ => (1 : ℝ≥0∞)) y ≤
        ENNReal.ofReal (min (1 : ℝ) (y ^ 2)) := by
    intro y
    by_cases hy : y ∈ Iic (-1 : ℝ)
    · have hle : y ≤ (-1 : ℝ) := by
        simpa only [Set.mem_Iic] using hy
      have hs : (1 : ℝ) ≤ y ^ 2 := by
        nlinarith [sq_nonneg (y + 1)]
      have hmin : min (1 : ℝ) (y ^ 2) = 1 :=
        min_eq_left hs
      simp [Set.indicator, hy, hmin]
    · simp [Set.indicator, hy]
  have hbound :
      ν (Iic (-1 : ℝ)) ≤
        ∫⁻ y : ℝ, ENNReal.ofReal (min (1 : ℝ) (y ^ 2)) ∂ν := by
    calc
      ν (Iic (-1 : ℝ)) =
          ∫⁻ y : ℝ,
            (Iic (-1 : ℝ)).indicator (fun _ : ℝ => (1 : ℝ≥0∞)) y ∂ν := by
        simpa using
          (lintegral_indicator_one (μ := ν) (measurableSet_Iic : MeasurableSet (Iic (-1 : ℝ)))).symm
      _ ≤ _ := lintegral_mono hpoint
  exact (lt_of_le_of_lt hbound hν).ne
