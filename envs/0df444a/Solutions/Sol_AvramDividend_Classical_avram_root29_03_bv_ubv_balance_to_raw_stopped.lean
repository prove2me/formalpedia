-- Prove2me | solution 1 for AvramDividend.Classical.avram_root29_03_bv_ubv_balance_to_raw_stopped
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-29T11:12:22.934031+00:00
-- url     : https://prove2.me/submissions/7b7c0c33-6beb-42b6-9189-259ff0ebf471

import Mathlib.Analysis.Complex.Exponential
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Definitions.Def_AvramDividend_Classical_TwoSidedExit
import Theorems.Thm_AvramDividend_Classical_avram_root29_03_raw_exit_scale_product_eq_stopped_terminal
import Theorems.Thm_AvramDividend_Classical_avram_root29_03_standing_stopped_min_terminal_factorisation
import Theorems.Thm_AvramDividend_Classical_avram_root29_03_exact_qscale_two_branch_terminal_conversion

open AvramDividend.Classical MeasureTheory Set Filter Topology
open scoped NNReal ENNReal

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

/-- The actual BV stopped OST balance and UBV strict two-payoff killed
balance, given explicitly for their respective cases, imply the exact raw
strict upper-before-ruin stopped-scale identity without any Open import. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (q : ℝ) (hq : 0 < q)
    (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (a x : ℝ) (ha : 0 < a) (hx0 : 0 ≤ x) (hxa : x ≤ a)
    (hBVBalance : X.BoundedVariation →
      twoSidedExitExpectation X q a x * ENNReal.ofReal (W a) =
        ENNReal.ofReal (W x))
    (hUBVBalance : ¬ X.BoundedVariation →
      (∫⁻ ω,
      (if twoSidedExitUpTime X (a - x) ω <
          twoSidedExitDownTime X (-x) ω then
        ENNReal.ofReal
          (Real.exp (-(q * ENNReal.toReal (twoSidedExitUpTime X (a - x) ω)))) *
          ENNReal.ofReal
            (W (x + X.X (twoSidedExitUpTime X (a - x) ω).toNNReal ω)) else 0) +
      (if twoSidedExitDownTime X (-x) ω <
          twoSidedExitUpTime X (a - x) ω then
        ENNReal.ofReal
          (Real.exp (-(q * ENNReal.toReal (twoSidedExitDownTime X (-x) ω)))) *
          ENNReal.ofReal
            (W (x + X.X (twoSidedExitDownTime X (-x) ω).toNNReal ω)) else 0) ∂P) = ENNReal.ofReal (W x)) :
    (∫⁻ ω,
      if (⨅ (t : ℝ≥0) (_ : a - x < X.X t ω), (t : ℝ≥0∞)) <
          (⨅ (t : ℝ≥0) (_ : X.X t ω < -x), (t : ℝ≥0∞)) then
        ENNReal.ofReal
          (Real.exp (-(q * ENNReal.toReal
            (⨅ (t : ℝ≥0) (_ : a - x < X.X t ω), (t : ℝ≥0∞)))))
      else 0 ∂P) * ENNReal.ofReal (W a) = ENNReal.ofReal (W x) := by
  have hRaw :=
    avram_root29_03_raw_exit_scale_product_eq_stopped_terminal
      X hX q hq W hW a x ha hx0 hxa
  by_cases hBV : X.BoundedVariation
  · have hTerm :=
      avram_root29_03_standing_stopped_min_terminal_factorisation
        X hX q hq W hW a x ha hx0 hxa
    exact hRaw.trans (hTerm.trans (hBVBalance hBV))
  · have hTerm :=
      avram_root29_03_exact_qscale_two_branch_terminal_conversion
        X q W hW a x ha hxa
    exact hRaw.trans (hTerm.trans (hUBVBalance hBV))
