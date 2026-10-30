-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave3_02_cstar_value_of_local_differentiability
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-30T00:32:17.554644+00:00
-- url     : https://prove2.me/submissions/c853ff4a-ca88-41be-b4bb-4a0e6f804a4f

import Mathlib.Analysis.Calculus.FDeriv.Defs
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Definitions.Def_AvramDividend_Classical_ReflectionBarrier
import Theorems.Thm_AvramDividend_Classical_scaleFunction_tilted_positive_monotone
import Theorems.Thm_AvramDividend_Classical_normalized_derivative_lower_bound
import Theorems.Thm_AvramDividend_Classical_avram_wave3_02_all_capital_of_local_deriv_nonzero
import Theorems.Thm_AvramDividend_Classical_barrier_strategy_value_zero_all_capital

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

/-- The all-capital cstar reflected value needs only differentiability at cstar
when the optimal barrier is positive; the zero barrier needs none. -/
theorem solution {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (q : ℝ) (hq : 0 < q) (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (hc : cstar W < ⊤)
    (hpoint : 0 < (cstar W).toReal →
      DifferentiableAt ℝ W (cstar W).toReal) :
    ∀ x : ℝ, 0 ≤ x →
      dividendValue X q x (barrierStrategy X x (cstar W).toReal) =
        ENNReal.ofReal (vcstar W x) := by
  intro x hx
  let a : ℝ := (cstar W).toReal
  change dividendValue X q x (barrierStrategy X x a) =
    ENNReal.ofReal (barrierValue W a x)
  have ha0 : 0 ≤ a := ENNReal.toReal_nonneg
  by_cases hzero : a = 0
  · simpa [hzero] using
      (barrier_strategy_value_zero_all_capital X hX q hq W hW x hx)
  · have ha : 0 < a := lt_of_le_of_ne ha0 (Ne.symm hzero)
    obtain ⟨hPos, φ, hφ, hMono⟩ :=
      scaleFunction_tilted_positive_monotone X hX q hq W hW
    have hBound : φ * W a ≤ deriv W a :=
      normalized_derivative_lower_bound φ a hMono ha (hpoint ha)
    have hdPos : 0 < deriv W a :=
      lt_of_lt_of_le (mul_pos hφ (hPos a ha)) hBound
    exact avram_wave3_02_all_capital_of_local_deriv_nonzero
      X hX q hq W hW a ha (ne_of_gt hdPos) x hx
