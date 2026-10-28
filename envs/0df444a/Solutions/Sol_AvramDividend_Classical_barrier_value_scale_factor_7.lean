-- Prove2me | solution 7 for AvramDividend.Classical.barrier_value_scale_factor
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-25T07:08:01.288306+00:00
-- url     : https://prove2.me/submissions/44847116-40ea-4cc9-9c93-8f06a8c1005a
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_AvramDividend_Classical_scaleFunction_strict_pos_of_standing
import Theorems.Thm_AvramDividend_Classical_barrierStrategy_value_eq_exit_factor

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

/-- Identify the barrier value at initial capital from the exit factor
and normalise the upper-barrier payoff using strict positivity of W. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (q : ℝ) (hq : 0 < q)
    (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (a : ℝ) (ha : 0 < a) (x : ℝ) (hx0 : 0 ≤ x) (hxa : x ≤ a) :
    0 < W a ∧
      dividendValue X q x (barrierStrategy X x a) =
        ENNReal.ofReal (W x / W a) *
          dividendValue X q a (barrierStrategy X a a) := by
  have hWa : 0 < W a :=
    scaleFunction_strict_pos_of_standing X hX q hq W hW a ha
  have hquot : W a / W a = 1 := div_self (ne_of_gt hWa)
  have hboundary :
      dividendValue X q a (barrierStrategy X a a) =
        barrierSupValue X a q := by
    simpa [hquot] using
      (barrierStrategy_value_eq_exit_factor X hX q hq W hW
        a ha a (le_of_lt ha) le_rfl)
  refine ⟨hWa, ?_⟩
  calc
    dividendValue X q x (barrierStrategy X x a) =
        ENNReal.ofReal (W x / W a) * barrierSupValue X a q :=
      barrierStrategy_value_eq_exit_factor X hX q hq W hW
        a ha x hx0 hxa
    _ = ENNReal.ofReal (W x / W a) *
        dividendValue X q a (barrierStrategy X a a) := by
      rw [← hboundary]
