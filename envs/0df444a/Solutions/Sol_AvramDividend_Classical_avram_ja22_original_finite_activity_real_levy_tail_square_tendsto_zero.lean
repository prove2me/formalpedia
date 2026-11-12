-- Prove2me | solution 1 for AvramDividend.Classical.avram_ja22_original_finite_activity_real_levy_tail_square_tendsto_zero
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-11T16:42:15.484961+00:00
-- url     : https://prove2.me/submissions/a0e1473a-bb44-4b28-b1a0-42e6c11f10a3

import Mathlib.Probability.Process.Filtration
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_anoise25_original_nearzero_gaussian_variance_integral_bound
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hFinite : X.ν (Iio (0 : ℝ)) ≠ ⊤) :
    Tendsto
      (fun n : ℕ =>
        ∫ z in Ioo (-(1 / ((n : ℝ) + 1))) 0, z ^ 2 ∂X.ν)
      atTop (nhds (0 : ℝ)) := by
  have heps : Tendsto (fun n : ℕ => (1 / ((n : ℝ) + 1) : ℝ))
      atTop (nhds 0) := tendsto_one_div_add_atTop_nhds_zero_nat
  have hupper : Tendsto
      (fun n : ℕ =>
        (1 / ((n : ℝ) + 1) : ℝ) ^ 2 *
          (X.ν (Iio (0 : ℝ))).toReal)
      atTop (nhds (0 : ℝ)) := by
    have hh := (heps.pow 2).mul_const
      ((X.ν (Iio (0 : ℝ))).toReal)
    convert hh using 1 <;> ring
  apply squeeze_zero
  · intro n
    exact (avram_anoise25_original_nearzero_gaussian_variance_integral_bound
      X hFinite n).1
  · intro n
    exact (avram_anoise25_original_nearzero_gaussian_variance_integral_bound
      X hFinite n).2
  · exact hupper
