-- Prove2me | solution 1 for AvramDividend.Classical.avram_gaussianB_real_L2_norm_equals_sqrt_second_moment
-- status  : ACCEPTED   (prove)
-- author  : @garyholm
-- created : 2026-11-18T03:05:44.432729+00:00
-- url     : https://prove2.me/submissions/efa87b77-b365-4417-8c9f-9287ac3b6bbe

import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
open MeasureTheory
open scoped ENNReal
noncomputable section

theorem solution
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (f : Ω → ℝ) (hf : MemLp f 2 P) :
    eLpNorm f 2 P =
      ENNReal.ofReal (Real.sqrt (∫ ω, (f ω) ^ 2 ∂P)) := by
  have h1 := hf.eLpNorm_eq_integral_rpow_norm (by norm_num) (by norm_num)
  rw [h1]
  congr 1
  rw [Real.sqrt_eq_rpow]
  congr 1
  · congr 1; ext ω; simp [Real.norm_eq_abs, sq_abs]
  · norm_num
