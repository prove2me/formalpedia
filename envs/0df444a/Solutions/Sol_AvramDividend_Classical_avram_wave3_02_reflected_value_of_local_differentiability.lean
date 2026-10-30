-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave3_02_reflected_value_of_local_differentiability
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-30T00:30:27.878985+00:00
-- url     : https://prove2.me/submissions/525ca4dd-b2db-4e9e-b19e-6c1bd6471db9

import Mathlib.Analysis.Calculus.FDeriv.Defs
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Definitions.Def_AvramDividend_Classical_ReflectionBarrier
import Theorems.Thm_AvramDividend_Classical_scaleFunction_tilted_positive_monotone
import Theorems.Thm_AvramDividend_Classical_normalized_derivative_lower_bound
import Theorems.Thm_AvramDividend_Classical_avram_wave3_02_barrierSupValue_ratio_of_nonzero_deriv
import Theorems.Thm_AvramDividend_Classical_avram_wave3_02_all_capital_of_local_deriv_nonzero

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

/-- Pointwise differentiability at a positive barrier gives the original
reflected dividend ratio and every nonnegative initial-capital value. -/
theorem solution {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (q : ℝ) (hq : 0 < q) (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (a : ℝ) (ha : 0 < a) (hDa : DifferentiableAt ℝ W a) :
    (0 < deriv W a) ∧
    (barrierSupValue X a q = ENNReal.ofReal (W a / deriv W a)) ∧
    (∀ x : ℝ, 0 ≤ x →
      dividendValue X q x (barrierStrategy X x a) =
        ENNReal.ofReal (barrierValue W a x)) := by
  obtain ⟨hPos, φ, hφ, hMono⟩ :=
    scaleFunction_tilted_positive_monotone X hX q hq W hW
  have hBound : φ * W a ≤ deriv W a :=
    normalized_derivative_lower_bound φ a hMono ha hDa
  have hdPos : 0 < deriv W a :=
    lt_of_lt_of_le (mul_pos hφ (hPos a ha)) hBound
  refine ⟨hdPos, ?_, ?_⟩
  · exact avram_wave3_02_barrierSupValue_ratio_of_nonzero_deriv
      X hX q hq W hW a ha (ne_of_gt hdPos)
  · exact avram_wave3_02_all_capital_of_local_deriv_nonzero
      X hX q hq W hW a ha (ne_of_gt hdPos)
