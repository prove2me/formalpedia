-- Prove2me | solution 1 for AvramDividend.Classical.avram_bvb52_original_finite_negative_rate_times_uniform_last_strip_width_zero
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-13T13:01:51.115783+00:00
-- url     : https://prove2.me/submissions/6f3dec12-12e7-43b9-bb69-b60732b7c268

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p3_grid4_original_uniform_strict_mesh_cofinal_at_horizon
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Classical MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

/-- The physical predictable negative-mark intensity of the original
finite-activity source multiplied by its prescribed last mesh width tends zero. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hFinite : X.ν (Iio (0 : ℝ)) < ⊤)
    (T : ℝ) (hT : 0 < T) :
    Tendsto (fun n : ℕ =>
      (X.ν (Iio (0 : ℝ))).toReal *
        (T / ((n : ℝ) + 2))) atTop (𝓝 (0 : ℝ)) := by
  have hEnd :=
    (avram_p3_grid4_original_uniform_strict_mesh_cofinal_at_horizon T hT).2
  have hDelta : Tendsto (fun n : ℕ =>
      T / ((n : ℝ) + 2)) atTop (𝓝 (0 : ℝ)) := by
    have h := (tendsto_const_nhds (x := T)).sub hEnd
    convert h using 1 <;> simp
  simpa using hDelta.const_mul (X.ν (Iio (0 : ℝ))).toReal
