-- Prove2me | solution 1 for AvramDividend.Classical.vcstar_ge_excess_reserve_above_cstar
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-25T15:45:04.364995+00:00
-- url     : https://prove2.me/submissions/215fdd09-46aa-4b14-894d-f08494e2c4db

import Mathlib.Tactic.Linarith
import Theorems.Thm_AvramDividend_Classical_barrierValue_nonnegative_for_nonnegative_capital
import Theorems.Thm_AvramDividend_Classical_vcstar_eq_linear_gt_cstar
import Mathlib.Data.ENNReal.Basic
import Mathlib.MeasureTheory.MeasurableSpace.Defs

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

/-- Above its barrier, the dividend value dominates the immediately
available surplus over that barrier. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (q : ℝ) (hq : 0 < q) (W : ℝ → ℝ)
    (hW : IsScaleFunction X q W) (x : ℝ)
    (hx : (cstar W).toReal < x) :
    x - (cstar W).toReal ≤ vcstar W x := by
  let a : ℝ := (cstar W).toReal
  have ha : 0 ≤ a := ENNReal.toReal_nonneg
  have hb : 0 ≤ barrierValue W a a :=
    barrierValue_nonnegative_for_nonnegative_capital
      X hX q hq W hW a a ha ha
  have hboundary : barrierValue W a a =
      divE (W a) (scaleDeriv W a) := by
    simp [barrierValue, not_lt.mpr ha]
  have hval : vcstar W x = x - a + barrierValue W a a := by
    calc
      vcstar W x = x - a + divE (W a) (scaleDeriv W a) :=
        vcstar_eq_linear_gt_cstar W x hx
      _ = x - a + barrierValue W a a := by rw [hboundary]
  change x - a ≤ vcstar W x
  rw [hval]
  linarith
