-- Prove2me | solution 1 for AvramDividend.Classical.avram_bvb22_original_cp_noarrival_tenth_positive_probability
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-13T00:25:50.036019+00:00
-- url     : https://prove2.me/submissions/1040833e-b569-4552-a23c-98c7df4d1510

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_a06_original_cp_interarrival_survival
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Classical MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem solution
    (P : Measure ((ℕ → ℝ) × (ℕ → ℝ))) [IsProbabilityMeasure P]
    (τ Y : ℕ → ((ℕ → ℝ) × (ℕ → ℝ)) → ℝ)
    (hd : LevyFoundations.IsCompoundPoissonDriver τ Y (1 : ℝ≥0)
      ((volume : Measure ℝ).restrict (Ioo (-1 : ℝ) 0)) P) :
    P {ω | (1 / 10 : ℝ) < τ 0 ω} =
      ENNReal.ofReal (Real.exp (-(1 / 10 : ℝ))) ∧
    0 < P {ω | (1 / 10 : ℝ) < τ 0 ω}  := by
  have heq :=
    avram_a06_original_cp_interarrival_survival P τ Y hd 0 (1 / 10)
      (by norm_num)
  constructor
  · exact heq
  · rw [heq]
    exact ENNReal.ofReal_pos.mpr (Real.exp_pos _)
