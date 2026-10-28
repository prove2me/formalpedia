-- Prove2me | solution 1 for AvramDividend.Classical.nonnegative_real_convolution_lconvolution_ofReal_bridge
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-25T10:12:37.76968+00:00
-- url     : https://prove2.me/submissions/5c29e6c4-2258-4946-a23c-40d48499fcee

import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Constructions.BorelSpace.Real
import Mathlib.Analysis.LConvolution
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Data.ENNReal.Real
import Mathlib.Tactic.Ring
open MeasureTheory
open scoped NNReal ENNReal
theorem solution
    (κ f : ℝ → ℝ) (x : ℝ)
    (hκ : ∀ y : ℝ, 0 ≤ κ y) (hf : ∀ y : ℝ, 0 ≤ f y)
    (hint : Integrable (fun y : ℝ => κ y * f (x - y)) volume) :
    lconvolution (fun y : ℝ => ENNReal.ofReal (κ y))
        (fun y : ℝ => ENNReal.ofReal (f y)) volume x =
      ENNReal.ofReal (∫ y : ℝ, κ y * f (x - y) ∂volume) := by
  rw [lconvolution_def, ofReal_integral_eq_lintegral_ofReal hint
    (Filter.Eventually.of_forall fun y => mul_nonneg (hκ y) (hf _))]
  refine lintegral_congr fun y => ?_
  rw [← ENNReal.ofReal_mul (hκ y), neg_add_eq_sub]
