-- Prove2me | solution 1 for AvramDividend.Classical.bv_actual_origin_zero_deficit_path_cylinder_ae_ws01c
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-28T23:46:01.687742+00:00
-- url     : https://prove2.me/submissions/4fa67663-f6f7-4dda-9c87-28b6b622606b

import Mathlib
import Theorems.Thm_AvramDividend_Classical_bv_actual_origin_dyadic_deficit_zero_ae_ws01c

open MeasureTheory Filter Topology AvramDividend.Classical
open scoped NNReal

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {ℱ : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P ℱ) (hBV : X.BoundedVariation) :
    ∀ᵐ ω ∂P,
      Tendsto (fun n : ℕ =>
        (X.drift * ((((1 : ℝ≥0) / 2) ^ n : ℝ≥0) : ℝ) -
          X.X (((1 : ℝ≥0) / 2) ^ n) ω) /
            ((((1 : ℝ≥0) / 2) ^ n : ℝ≥0) : ℝ))
        atTop (𝓝 (0 : ℝ)) := by
  filter_upwards [bv_actual_origin_dyadic_deficit_zero_ae_ws01c X hBV] with ω hω
  refine hω.congr fun n => ?_
  have hpos : (0 : ℝ) < ((((1 : ℝ≥0) / 2) ^ n : ℝ≥0) : ℝ) := by positivity
  rw [X.X_zero ω, sub_zero]
  push_cast at hpos ⊢
  field_simp
