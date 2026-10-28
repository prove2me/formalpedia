-- Prove2me | solution 2 for AvramDividend.Classical.killed_nextRecord_discount_le_shifted_twoSided_of_strict_exit_inclusion
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-25T22:46:34.572029+00:00
-- url     : https://prove2.me/submissions/7817b7c2-9696-42bc-a35a-88eea6dff7ac

import Definitions.Def_AvramDividend_Classical_TwoSidedExit
import Theorems.Thm_AvramDividend_Classical_survived_nextRecord_shifted_upclock_le_lower_exit
import Mathlib.Data.ENNReal.Basic
import Theorems.Thm_AvramDividend_Classical_nextRecord_discount_eq_past_mul_future

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (a b ε q : ℝ) (hε : 0 ≤ ε) (ω : Ω) (u : ℝ≥0)
    (hu : (u : ℝ≥0∞) = twoSidedExitUpTime X b ω)
    (hAt : X.X u ω = b)
    (ρ σ : ℝ≥0∞)
    (hρ : ρ = (⨅ (t : ℝ≥0)
        (_ : ε < X.X (u + t) ω - X.X u ω), (t : ℝ≥0∞)))
    (hρfinite : ρ ≠ ⊤)
    (hInclusion : twoSidedExitUpTime X (b + ε) ω <
      barrierRuinTime X a ω → ρ < σ) :
    (if twoSidedExitUpTime X (b + ε) ω < barrierRuinTime X a ω then
      ENNReal.ofReal ε *
        ENNReal.ofReal (Real.exp (-(q *
          (twoSidedExitUpTime X (b + ε) ω).toReal)))
      else 0) ≤
    ENNReal.ofReal ε *
      (ENNReal.ofReal (Real.exp (-(q * (u : ℝ)))) *
        (if ρ < σ then
          ENNReal.ofReal (Real.exp (-(q * ρ.toReal)))
        else 0)) := by
  by_cases hSurvive :
      twoSidedExitUpTime X (b + ε) ω < barrierRuinTime X a ω
  · have hFactor := nextRecord_discount_eq_past_mul_future
      X b ε q hε u ω hu hAt ρ hρ hρfinite
    simp [hSurvive, hInclusion hSurvive, hFactor]
  · simp [hSurvive]
