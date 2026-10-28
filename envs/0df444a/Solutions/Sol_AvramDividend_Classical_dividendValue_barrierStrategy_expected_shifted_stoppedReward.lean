-- Prove2me | solution 1 for AvramDividend.Classical.dividendValue_barrierStrategy_expected_shifted_stoppedReward
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-26T23:15:41.495368+00:00
-- url     : https://prove2.me/submissions/bbda3dba-d646-4369-a242-32f2d94dd864

import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Mathlib.Data.ENNReal.Basic
import Theorems.Thm_AvramDividend_Classical_dividendValue_barrierStrategy_rawTwoSidedExit_support
import Theorems.Thm_AvramDividend_Classical_barrierStrategy_stoppedReward_postUpcrossing_shifted_window
import Theorems.Thm_AvramDividend_Classical_shiftedSup_dividendMeasure_zero_nonpositive_of_levy
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
            ((fun t : ℝ => (u : ℝ) + t) ⁻¹'
              paymentTimes (ruinTime X x (barrierStrategy X x a) ω)),
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
  by_cases hA : (⨅ (s : ℝ≥0) (_ : a - x < X.X s ω), (s : ℝ≥0∞)) < (⨅ (s : ℝ≥0) (_ : X.X s ω < -x), (s : ℝ≥0∞))
  · have hfin : (⨅ (s : ℝ≥0) (_ : a - x < X.X s ω), (s : ℝ≥0∞)) ≠ ⊤ := by
      intro htop
      rw [htop] at hA
      exact not_top_lt hA
    have hu : (((⨅ (s : ℝ≥0) (_ : a - x < X.X s ω), (s : ℝ≥0∞)).toNNReal) : ℝ≥0∞) = (⨅ (s : ℝ≥0) (_ : a - x < X.X s ω), (s : ℝ≥0∞)) := by
      exact ENNReal.coe_toNNReal hfin
    simp only [hA, ite_true]
    exact barrierStrategy_stoppedReward_postUpcrossing_shifted_window
      X x a hx0 hxa q ω ((⨅ (s : ℝ≥0) (_ : a - x < X.X s ω), (s : ℝ≥0∞)).toNNReal) hu
      (shiftedSup_dividendMeasure_zero_nonpositive_of_levy
        X ω ((⨅ (s : ℝ≥0) (_ : a - x < X.X s ω), (s : ℝ≥0∞)).toNNReal))
  · simp only [hA, ite_false]
