-- Prove2me | solution 1 for AvramDividend.Classical.barrierStrategy_postUpcrossing_discounted_dividend_translation
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-26T10:37:54.855253+00:00
-- url     : https://prove2.me/submissions/b767769c-4a88-4b4f-a9ce-6d45b7990e5a

import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Mathlib.Tactic.Linarith
import Theorems.Thm_AvramDividend_Classical_barrierStrategy_dividendMeasure_map_shift_of_support
import Theorems.Thm_AvramDividend_Classical_barrierStrategy_dividendMeasure_zero_nonpositive
import Theorems.Thm_AvramDividend_Classical_dividendMeasure_locallyFinite
import Theorems.Thm_AvramDividend_Classical_lintegral_killed_discount_translation_of_measure_map
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
    (x a : ℝ) (hx0 : 0 ≤ x) (hxa : x ≤ a)
    (q : ℝ) (ω : Ω) (u : ℝ≥0)
    (hu : (u : ℝ≥0∞) =
      (⨅ (s : ℝ≥0) (_ : a - x < X.X s ω), (s : ℝ≥0∞)))
    (hνneg : (dividendMeasure
      (fun r (_ : Ω) =>
        sSup ((fun v : ℝ≥0 => X.X (u + v) ω - X.X u ω) '' Set.Icc 0 r))
      ω) (Set.Iic (0 : ℝ)) = 0) :
    (∫⁻ t in Set.Ioi (u : ℝ),
      ENNReal.ofReal (Real.exp (-(q * t)))
      ∂(dividendMeasure (barrierStrategy X x a) ω)) =
    ENNReal.ofReal (Real.exp (-(q * (u : ℝ)))) *
      (∫⁻ t in Set.Ioi (0 : ℝ),
        ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure
      (fun r (_ : Ω) =>
        sSup ((fun v : ℝ≥0 => X.X (u + v) ω - X.X u ω) '' Set.Icc 0 r))
      ω)) := by
  classical
  let μ : Measure ℝ := dividendMeasure (barrierStrategy X x a) ω
  let ν : Measure ℝ :=
    dividendMeasure
      (fun r (_ : Ω) =>
        sSup ((fun v : ℝ≥0 => X.X (u + v) ω - X.X u ω) '' Set.Icc 0 r))
      ω
  letI : IsLocallyFiniteMeasure μ := by
    dsimp [μ]
    exact dividendMeasure_locallyFinite (barrierStrategy X x a) ω
  have hμneg : μ (Set.Iic (0 : ℝ)) = 0 := by
    exact barrierStrategy_dividendMeasure_zero_nonpositive X x a hx0 hxa ω
  have hμ : μ = Measure.map (fun t : ℝ => (u : ℝ) + t) ν := by
    exact barrierStrategy_dividendMeasure_map_shift_of_support
      X x a hx0 hxa ω u hu hμneg hνneg
  have hwindow (t : ℝ) :
      (u : ℝ) + t ∈ Set.Ioi (u : ℝ) ↔ t ∈ Set.Ioi (0 : ℝ) := by
    simp only [Set.mem_Ioi]
    constructor <;> intro ht <;> linarith
  exact lintegral_killed_discount_translation_of_measure_map
    μ ν (u : ℝ) q (Set.Ioi (u : ℝ)) (Set.Ioi (0 : ℝ))
    measurableSet_Ioi measurableSet_Ioi hμ hwindow