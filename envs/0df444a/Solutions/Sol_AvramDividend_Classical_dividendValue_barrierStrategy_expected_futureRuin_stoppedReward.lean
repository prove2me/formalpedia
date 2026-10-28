-- Prove2me | solution 1 for AvramDividend.Classical.dividendValue_barrierStrategy_expected_futureRuin_stoppedReward
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-26T23:40:28.849593+00:00
-- url     : https://prove2.me/submissions/e94e8a85-bc93-4ac6-bc37-3ebfb37ccd14

import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Mathlib.Data.ENNReal.Basic
import Theorems.Thm_AvramDividend_Classical_dividendValue_barrierStrategy_rawTwoSidedExit_support
import Theorems.Thm_AvramDividend_Classical_barrierStrategy_upExit_before_controlledRuin_iff_rawExit
import Theorems.Thm_AvramDividend_Classical_barrierStrategy_stoppedReward_shifted_ruin_window
import Mathlib.Analysis.Complex.Exponential
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

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
  classical
  rw [dividendValue_barrierStrategy_rawTwoSidedExit_support
    X q x a ha hx0 hxa]
  apply lintegral_congr
  intro ω
  by_cases hA :
      (⨅ (s : ℝ≥0) (_ : a - x < X.X s ω), (s : ℝ≥0∞)) <
      (⨅ (s : ℝ≥0) (_ : X.X s ω < -x), (s : ℝ≥0∞))
  · have hfin :
        (⨅ (s : ℝ≥0) (_ : a - x < X.X s ω), (s : ℝ≥0∞)) ≠ ⊤ := by
      intro htop
      rw [htop] at hA
      exact not_top_lt hA
    let u : ℝ≥0 :=
      (⨅ (s : ℝ≥0) (_ : a - x < X.X s ω), (s : ℝ≥0∞)).toNNReal
    have hu : (u : ℝ≥0∞) =
        (⨅ (s : ℝ≥0) (_ : a - x < X.X s ω), (s : ℝ≥0∞)) := by
      exact ENNReal.coe_toNNReal hfin
    have hsuccess : (u : ℝ≥0∞) <
        ruinTime X x (barrierStrategy X x a) ω := by
      rw [hu]
      exact (barrierStrategy_upExit_before_controlledRuin_iff_rawExit
        X x a ha hx0 hxa ω).mpr hA
    simp only [hA, ite_true]
    exact barrierStrategy_stoppedReward_shifted_ruin_window
      X x a hx0 hxa q ω u hu hsuccess
  · simp only [hA, ite_false]
