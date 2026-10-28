-- Prove2me | solution 1 for AvramDividend.Classical.shifted_twoSided_exit_killed_discount_eq_product
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-25T18:55:15.505263+00:00
-- url     : https://prove2.me/submissions/cbdd2a37-0825-443c-b666-745e9c72d726

import Mathlib.Data.ENNReal.Basic
import Mathlib.Analysis.Complex.Exponential
import Definitions.Def_AvramDividend_Classical_TwoSidedExit
import Theorems.Thm_AvramDividend_Classical_shifted_twoSided_firstExit_implies_nextRecord_killed
import Theorems.Thm_AvramDividend_Classical_nextRecord_discount_eq_past_mul_future

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (a b ε q : ℝ) (ha : 0 < a) (hb : 0 ≤ b) (hε : 0 ≤ ε)
    (ω : Ω) (u T : ℝ≥0)
    (hu : (u : ℝ≥0∞) = twoSidedExitUpTime X b ω)
    (hAt : X.X u ω = b)
    (hBefore : (u : ℝ≥0∞) < barrierRuinTime X a ω)
    (hUp : (T : ℝ≥0∞) =
      (⨅ (r : ℝ≥0)
        (_ : ε < X.X (u + r) ω - X.X u ω), (r : ℝ≥0∞)))
    (hUpBeforeDown : (T : ℝ≥0∞) <
      (⨅ (r : ℝ≥0)
        (_ : X.X (u + r) ω - X.X u ω < ε - a),
        (r : ℝ≥0∞))) :
    (if twoSidedExitUpTime X (b + ε) ω < barrierRuinTime X a ω then
        ENNReal.ofReal (ε * Real.exp
          (-(q * (twoSidedExitUpTime X (b + ε) ω).toReal)))
      else 0) =
      ENNReal.ofReal ε *
        (ENNReal.ofReal (Real.exp (-(q * (u : ℝ)))) *
          ENNReal.ofReal (Real.exp (-(q * (T : ℝ))))) := by
  rw [if_pos (AvramDividend.Classical.shifted_twoSided_firstExit_implies_nextRecord_killed X a b ε ha hb hε ω u T
    hu hAt hBefore hUp hUpBeforeDown), ENNReal.ofReal_mul hε,
    AvramDividend.Classical.nextRecord_discount_eq_past_mul_future X b ε q hε u ω hu hAt (T : ℝ≥0∞) hUp
      ENNReal.coe_ne_top, ENNReal.coe_toReal]
