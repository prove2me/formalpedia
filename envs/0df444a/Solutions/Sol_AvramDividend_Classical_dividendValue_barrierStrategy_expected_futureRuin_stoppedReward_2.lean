-- Prove2me | solution 2 for AvramDividend.Classical.dividendValue_barrierStrategy_expected_futureRuin_stoppedReward
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-26T23:41:26.378859+00:00
-- url     : https://prove2.me/submissions/b51d2e34-a30d-4bed-b4a4-4e4f878adbef

import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Mathlib.Data.ENNReal.Basic
import Theorems.Thm_AvramDividend_Classical_dividendValue_barrierStrategy_rawTwoSidedExit_support
import Theorems.Thm_AvramDividend_Classical_barrierStrategy_upExit_before_controlledRuin_iff_rawExit
import Theorems.Thm_AvramDividend_Classical_barrierStrategy_stoppedReward_shifted_ruin_window
open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q x a : ℝ) (ha : 0 < a) (hx0 : 0 ≤ x) (hxa : x ≤ a) :
    dividendValue X q x (barrierStrategy X x a) =
      ∫⁻ ω, if (⨅ (s : ℝ≥0) (_ : a - x < X.X s ω), (s : ℝ≥0∞)) < (⨅ (s : ℝ≥0) (_ : X.X s ω < -x), (s : ℝ≥0∞)) then
        let u : ℝ≥0 := ((⨅ (s : ℝ≥0) (_ : a - x < X.X s ω), (s : ℝ≥0∞)).toNNReal)
        ENNReal.ofReal (Real.exp (-(q * (u : ℝ)))) *
          (∫⁻ t in Set.Ioi (0 : ℝ) ∩
            paymentTimes
              (⨅ (r : ℝ≥0)
                (_ : a + (X.X (u + r) ω - X.X u ω) <
                  max 0
                    (sSup ((fun z : ℝ≥0 => X.X (u + z) ω) '' Set.Icc 0 r) -
                      X.X u ω)), (r : ℝ≥0∞)),
            ENNReal.ofReal (Real.exp (-(q * t))) ∂
              (dividendMeasure
                (fun r (_ : Ω) =>
                  sSup ((fun v : ℝ≥0 =>
                    X.X (u + v) ω - X.X u ω) '' Set.Icc 0 r))
                ω))
      else 0 ∂P := by
  rw [dividendValue_barrierStrategy_rawTwoSidedExit_support X q x a ha hx0 hxa]
  refine lintegral_congr fun ω => ?_
  split_ifs with h
  · have hfin : (⨅ (s : ℝ≥0) (_ : a - x < X.X s ω), (s : ℝ≥0∞)) ≠ ⊤ := ne_top_of_lt h
    have hu : (((⨅ (s : ℝ≥0) (_ : a - x < X.X s ω), (s : ℝ≥0∞)).toNNReal : ℝ≥0) : ℝ≥0∞) =
        (⨅ (s : ℝ≥0) (_ : a - x < X.X s ω), (s : ℝ≥0∞)) := ENNReal.coe_toNNReal hfin
    have hs := (barrierStrategy_upExit_before_controlledRuin_iff_rawExit X x a ha hx0 hxa ω).2 h
    rw [← hu] at hs
    exact barrierStrategy_stoppedReward_shifted_ruin_window X x a hx0 hxa q ω _ hu hs
  · rfl
