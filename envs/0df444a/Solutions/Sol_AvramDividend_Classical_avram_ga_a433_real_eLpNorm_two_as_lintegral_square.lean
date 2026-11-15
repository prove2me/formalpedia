-- Prove2me | solution 1 for AvramDividend.Classical.avram_ga_a433_real_eLpNorm_two_as_lintegral_square
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-14T23:58:52.323012+00:00
-- url     : https://prove2.me/submissions/f0c352d4-b5c8-47d5-9018-ac6900f0d86d

import Mathlib.MeasureTheory.Function.LpSeminorm.Defs
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ENNReal Filter
open scoped NNReal ENNReal
noncomputable section

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {μ : Measure Ω} (f : Ω → ℝ) :
    eLpNorm f 2 μ =
      (∫⁻ ω, (‖f ω‖₊ : ℝ≥0∞) ^ 2 ∂μ) ^ ((1 : ℝ) / 2) := by
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num) (by norm_num)]
  simp only [ENNReal.toReal_ofNat]
  congr 1
  refine lintegral_congr fun ω => ?_
  rw [← ENNReal.rpow_natCast _ 2]
  norm_num
  simp [enorm_eq_nnnorm]
