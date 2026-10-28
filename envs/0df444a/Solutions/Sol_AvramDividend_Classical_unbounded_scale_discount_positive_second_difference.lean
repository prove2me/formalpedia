-- Prove2me | solution 1 for AvramDividend.Classical.unbounded_scale_discount_positive_second_difference
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-25T15:49:46.936509+00:00
-- url     : https://prove2.me/submissions/b1b52ea1-d9b0-40a6-8299-e7ed188eacf9

import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Theorems.Thm_AvramDividend_Classical_unbounded_scale_discount_strict_convex_secants
import Mathlib.MeasureTheory.MeasurableSpace.Defs
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

/-- Every positive finite discount increment has a strictly positive second difference. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hnbv : ¬ X.BoundedVariation)
    (W : ℝ → ℝ → ℝ)
    (hW : ∀ q : ℝ, 0 ≤ q → IsScaleFunction X q (W q))
    (q h x : ℝ) (hq : 0 ≤ q) (hh : 0 < h) (hx : 0 < x) :
    0 < W (q + 2 * h) x - 2 * W (q + h) x + W q x := by
  have hq2 : 0 ≤ q + h := by linarith
  have hq3 : 0 ≤ q + 2 * h := by linarith
  have hq12 : q < q + h := by linarith
  have hq23 : q + h < q + 2 * h := by linarith
  have hs := unbounded_scale_discount_strict_convex_secants
    X hnbv q (q + h) (q + 2 * h)
    hq hq2 hq3 hq12 hq23
    (W q) (W (q + h)) (W (q + 2 * h))
    (hW q hq) (hW (q + h) hq2) (hW (q + 2 * h) hq3) x hx
  have hden1 : q + h - q = h := by ring
  have hden2 : q + 2 * h - (q + h) = h := by ring
  rw [hden1, hden2] at hs
  have hstep := (div_lt_div_iff_of_pos_right hh).mp hs
  linarith
