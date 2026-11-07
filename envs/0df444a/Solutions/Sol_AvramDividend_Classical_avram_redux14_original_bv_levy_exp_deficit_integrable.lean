-- Prove2me | solution 1 for AvramDividend.Classical.avram_redux14_original_bv_levy_exp_deficit_integrable
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-06T10:59:25.847113+00:00
-- url     : https://prove2.me/submissions/fcba2a0f-7f2d-418e-8afd-802c22ac7707

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_boundedVariation_min_one_abs_integrable

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Classical MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hBV : X.BoundedVariation) :
    IntegrableOn (fun y : ℝ => 1 - Real.exp y) (Iio (0 : ℝ)) X.ν := by
  have hbase :
      Integrable (fun y : ℝ => min (1 : ℝ) |y|) (X.ν.restrict (Iio (0 : ℝ))) :=
    boundedVariation_min_one_abs_integrable X hBV
  apply Integrable.mono' hbase
  · exact (continuous_const.sub Real.continuous_exp).aestronglyMeasurable
  · refine (ae_restrict_mem measurableSet_Iio).mono ?_
    intro y hy
    have hy0 : y < (0 : ℝ) := hy
    have hexp : Real.exp y ≤ 1 := by
      simpa using (Real.exp_le_exp.mpr hy0.le : Real.exp y ≤ Real.exp 0)
    have hb : y + 1 ≤ Real.exp y := Real.add_one_le_exp y
    have hpos : 0 ≤ 1 - Real.exp y := by linarith
    rw [Real.norm_eq_abs, abs_of_nonneg hpos]
    apply le_min
    · linarith [Real.exp_pos y]
    · rw [abs_of_nonpos hy0.le]
      linarith
