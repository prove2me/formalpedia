-- Prove2me | solution 1 for AvramDividend.Classical.avram_bvb57_original_compensator_last_strip_bounded_error_squeeze
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-13T23:48:27.135019+00:00
-- url     : https://prove2.me/submissions/890b10cb-cf74-475e-9643-97acb0400f5f

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_bvb52_original_finite_negative_rate_times_uniform_last_strip_width_zero
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Classical MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hFinite : X.ν (Iio (0 : ℝ)) < ⊤)
    (T : ℝ) (hT : 0 < T)
    (K : ℝ) (e : ℕ → ℝ)
    (hE : ∀ n : ℕ,
       -(K * ((X.ν (Iio (0 : ℝ))).toReal *
         (T / ((n : ℝ) + 2)))) ≤ e n ∧
       e n ≤ K * ((X.ν (Iio (0 : ℝ))).toReal *
         (T / ((n : ℝ) + 2)))) :
    Tendsto e atTop (𝓝 (0 : ℝ)) := by
  have hBase :=
    avram_bvb52_original_finite_negative_rate_times_uniform_last_strip_width_zero
      X hFinite T hT
  have hUpper : Tendsto (fun n : ℕ =>
      K * ((X.ν (Iio (0 : ℝ))).toReal * (T / ((n : ℝ) + 2))))
      atTop (𝓝 (0 : ℝ)) := by
    simpa only [mul_zero] using (tendsto_const_nhds.mul hBase)
  have hLower : Tendsto (fun n : ℕ =>
      -(K * ((X.ν (Iio (0 : ℝ))).toReal * (T / ((n : ℝ) + 2)))))
      atTop (𝓝 (0 : ℝ)) := by
    simpa only [neg_zero] using hUpper.neg
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le hLower hUpper
    (fun n => (hE n).1) (fun n => (hE n).2)
