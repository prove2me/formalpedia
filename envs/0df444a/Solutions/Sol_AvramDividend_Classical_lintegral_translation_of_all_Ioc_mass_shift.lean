-- Prove2me | solution 1 for AvramDividend.Classical.lintegral_translation_of_all_Ioc_mass_shift
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-25T18:17:23.864992+00:00
-- url     : https://prove2.me/submissions/9cf8f3b9-2646-4215-a882-5cc94aa22762

import Mathlib.MeasureTheory.Integral.Lebesgue.Map
import Theorems.Thm_AvramDividend_Classical_measure_eq_map_add_of_all_Ioc_translation

open MeasureTheory Set
open scoped ENNReal
theorem solution
    (μ ν : Measure ℝ) [IsLocallyFiniteMeasure μ]
    (u : ℝ)
    (hshift : ∀ a b : ℝ, a < b →
      μ (Set.Ioc (u + a) (u + b)) = ν (Set.Ioc a b))
    (f : ℝ → ℝ≥0∞) (hf : Measurable f) :
    (∫⁻ t : ℝ, f t ∂μ) =
      ∫⁻ t : ℝ, f (u + t) ∂ν := by
  rw [AvramDividend.Classical.measure_eq_map_add_of_all_Ioc_translation μ ν u hshift,
    lintegral_map hf (measurable_const_add u)]
