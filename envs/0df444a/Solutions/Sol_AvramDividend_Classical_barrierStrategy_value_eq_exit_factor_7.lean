-- Prove2me | solution 7 for AvramDividend.Classical.barrierStrategy_value_eq_exit_factor
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-25T06:17:03.342642+00:00
-- url     : https://prove2.me/submissions/549c97dc-fe75-4cce-8867-36818c3e0119

import Theorems.Thm_AvramDividend_Classical_barrierStrategy_value_eq_killed_exit_mul_supValue
import Theorems.Thm_AvramDividend_Classical_two_sided_exit_before_ruin_integral_identity

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

/-- Evaluate the killed-exit multiplier to obtain the scale-function ratio. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (q : ℝ) (hq : 0 < q)
    (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (a : ℝ) (ha : 0 < a) (x : ℝ) (hx0 : 0 ≤ x) (hxa : x ≤ a) :
    dividendValue X q x (barrierStrategy X x a) =
      ENNReal.ofReal (W x / W a) * barrierSupValue X a q := by
  rw [barrierStrategy_value_eq_killed_exit_mul_supValue X hX q hq a x ha hx0 hxa,
    two_sided_exit_before_ruin_integral_identity X hX q hq W hW a x ha hx0 hxa]
