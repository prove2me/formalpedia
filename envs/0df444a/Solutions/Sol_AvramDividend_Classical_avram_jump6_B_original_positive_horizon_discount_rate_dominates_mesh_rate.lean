-- Prove2me | solution 1 for AvramDividend.Classical.avram_jump6_B_original_positive_horizon_discount_rate_dominates_mesh_rate
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-19T20:32:47.262198+00:00
-- url     : https://prove2.me/submissions/2ebbf65c-04fb-4a92-be80-834303ff01dd

import Mathlib
import Definitions.Def_AvramDividend_Classical_DividendStrategy
open MeasureTheory Set Filter AvramDividend.Classical
noncomputable section
set_option autoImplicit false

theorem solution
    (q : ℝ) (hq : 0 < q) (n : ℕ) (hn : 0 < n)
    (j : ℕ) :
    q / ((j + 1 : ℕ) : ℝ) ≤
      q * ((n : ℝ) / ((j + 1 : ℕ) : ℝ)) *
        Real.exp (q * (n : ℝ)) := by
  have hq0 : 0 ≤ q := le_of_lt hq
  have hn1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hn0 : (0 : ℝ) ≤ (n : ℝ) := by positivity
  have hExp : (1 : ℝ) ≤ Real.exp (q * (n : ℝ)) := by
    apply Real.one_le_exp
    exact mul_nonneg hq0 hn0
  have hFactor : (1 : ℝ) ≤ (n : ℝ) * Real.exp (q * (n : ℝ)) := by
    calc
      (1 : ℝ) = (1 : ℝ) * 1 := by ring
      _ ≤ (n : ℝ) * 1 := mul_le_mul_of_nonneg_right hn1 (by norm_num)
      _ ≤ (n : ℝ) * Real.exp (q * (n : ℝ)) :=
        mul_le_mul_of_nonneg_left hExp hn0
  have hNonneg : 0 ≤ q / ((j + 1 : ℕ) : ℝ) := by positivity
  have hBound :=
    mul_le_mul_of_nonneg_left hFactor hNonneg
  calc
    q / ((j + 1 : ℕ) : ℝ) =
      (q / ((j + 1 : ℕ) : ℝ)) * 1 := by ring
    _ ≤ (q / ((j + 1 : ℕ) : ℝ)) *
        ((n : ℝ) * Real.exp (q * (n : ℝ))) := hBound
    _ = q * ((n : ℝ) / ((j + 1 : ℕ) : ℝ)) *
        Real.exp (q * (n : ℝ)) := by ring
