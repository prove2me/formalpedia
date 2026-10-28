-- Prove2me | solution 1 for AvramDividend.Classical.nextRecord_discount_eq_past_mul_future
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-25T18:34:19.790403+00:00
-- url     : https://prove2.me/submissions/08bb98f5-1a09-41ad-828b-90fd1e52af52

import Mathlib.Data.ENNReal.Basic
import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Theorems.Thm_AvramDividend_Classical_nextRecord_upclock_eq_add_shifted_inf
import Theorems.Thm_AvramDividend_Classical_discounted_dividend_weight_time_shift
import Mathlib.Analysis.Complex.Exponential

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory
open scoped NNReal ENNReal
open AvramDividend.Classical

/-! Split the finite next-record discount into stopped-past and future factors. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (b ε q : ℝ) (hε : 0 ≤ ε) (u : ℝ≥0) (ω : Ω)
    (hu : (u : ℝ≥0∞) = twoSidedExitUpTime X b ω)
    (hAt : X.X u ω = b)
    (ρ : ℝ≥0∞)
    (hρ : ρ =
      (⨅ (t : ℝ≥0)
        (_ : ε < X.X (u + t) ω - X.X u ω), (t : ℝ≥0∞)))
    (hρfinite : ρ ≠ ⊤) :
    ENNReal.ofReal (Real.exp
        (-(q * (twoSidedExitUpTime X (b + ε) ω).toReal))) =
      ENNReal.ofReal (Real.exp (-(q * (u : ℝ)))) *
        ENNReal.ofReal (Real.exp (-(q * ρ.toReal))) := by
  let t : ℝ≥0 := ρ.toNNReal
  have ht : (t : ℝ≥0∞) = ρ := ENNReal.coe_toNNReal hρfinite
  have hClock : twoSidedExitUpTime X (b + ε) ω =
      ((u + t : ℝ≥0) : ℝ≥0∞) := by
    rw [nextRecord_upclock_eq_add_shifted_inf X b ε hε u ω hu hAt]
    rw [← hρ, ← ht, ← ENNReal.coe_add]
  have hClockReal :
      (twoSidedExitUpTime X (b + ε) ω).toReal = ((u + t : ℝ≥0) : ℝ) := by
    rw [hClock, ENNReal.coe_toReal]
  have hFutureReal : ρ.toReal = (t : ℝ) := by
    rw [← ht, ENNReal.coe_toReal]
  rw [hClockReal, hFutureReal]
  exact discounted_dividend_weight_time_shift q u t
