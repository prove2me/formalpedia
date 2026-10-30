-- Prove2me | solution 10 for AvramDividend.Classical.bounded_variation_two_sided_exit_before_ruin_identity
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-28T13:02:14.923768+00:00
-- url     : https://prove2.me/submissions/76c22da6-d3a9-4e9e-9452-b003a754803a

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Definitions.Def_AvramDividend_Classical_TwoSidedExit
import Theorems.Thm_AvramDividend_Classical_bounded_variation_stopped_scale_balance
import Theorems.Thm_AvramDividend_Classical_scaleFunction_strict_pos_of_standing
import Theorems.Thm_AvramDividend_Classical_stopped_scale_identity_to_ratio

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set Filter Topology
open scoped NNReal ENNReal

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (q : ℝ) (hq : 0 < q)
    (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (hBV : X.BoundedVariation)
    (a x : ℝ) (ha : 0 < a) (hx0 : 0 ≤ x) (hxa : x ≤ a) :
    twoSidedExitExpectation X q a x = ENNReal.ofReal (W x / W a) := by
  -- Repair of CE 17631 E01-E03: add missing Theorems imports; bridge the
  -- raw-integral Open balance 2bb5 to the expectation form via unfolding,
  -- then close with Proved ratio algebra 212e and Proved positivity 59531.
  -- Sketch at best until Open 2bb5 is Proved.
  have hProd := AvramDividend.Classical.bounded_variation_stopped_scale_balance
    X hX q hq W hW hBV a x ha hx0 hxa
  have hWa : 0 < W a :=
    AvramDividend.Classical.scaleFunction_strict_pos_of_standing
      X hX q hq W hW a ha
  have hUnfold : twoSidedExitExpectation X q a x
      = (∫⁻ ω,
        if (⨅ (t : ℝ≥0) (_ : a - x < X.X t ω), (t : ℝ≥0∞)) <
            (⨅ (t : ℝ≥0) (_ : X.X t ω < -x), (t : ℝ≥0∞)) then
          ENNReal.ofReal
            (Real.exp (-(q * ENNReal.toReal
              (⨅ (t : ℝ≥0) (_ : a - x < X.X t ω), (t : ℝ≥0∞)))))
        else 0 ∂P) := by
    unfold twoSidedExitExpectation twoSidedExitUpTime twoSidedExitDownTime
    rfl
  have hBal : twoSidedExitExpectation X q a x * ENNReal.ofReal (W a)
      = ENNReal.ofReal (W x) := by
    rw [hUnfold]
    exact hProd
  exact AvramDividend.Classical.stopped_scale_identity_to_ratio
    (twoSidedExitExpectation X q a x) (W x) (W a) hBal hWa
