-- Prove2me | solution 1 for AvramDividend.Classical.avram_p2_b_rate_lintegral_normalised_weight_mul
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T22:30:46.066546+00:00
-- url     : https://prove2.me/submissions/3e4088fe-478a-4e7e-b5cf-7c78e79c9d78

import Mathlib.MeasureTheory.Integral.Lebesgue.Add
import Mathlib.Data.ENNReal.Basic

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter
open scoped ENNReal

theorem solution
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (f g : Ω → ℝ≥0∞) (hf : Measurable f) (hg : Measurable g)
    (c : ℝ≥0∞) :
    (∫⁻ ω, (f ω * c) * g ω ∂P) =
      (∫⁻ ω, f ω * g ω ∂P) * c := by
  calc
    (∫⁻ ω, (f ω * c) * g ω ∂P) =
        ∫⁻ ω, (f ω * g ω) * c ∂P := by
          apply lintegral_congr_ae
          filter_upwards [] with ω
          ac_rfl
    _ = (∫⁻ ω, f ω * g ω ∂P) * c :=
      lintegral_mul_const c (hf.mul hg)
