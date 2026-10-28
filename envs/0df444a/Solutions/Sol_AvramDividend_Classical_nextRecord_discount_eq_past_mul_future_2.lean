-- Prove2me | solution 2 for AvramDividend.Classical.nextRecord_discount_eq_past_mul_future
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-25T18:35:38.787992+00:00
-- url     : https://prove2.me/submissions/115ba055-36af-41c9-93df-12ae4ffb9bc9

import Mathlib.Data.ENNReal.Basic
import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Theorems.Thm_AvramDividend_Classical_nextRecord_upclock_eq_add_shifted_inf
import Theorems.Thm_AvramDividend_Classical_discounted_dividend_weight_time_shift

open MeasureTheory
open scoped NNReal ENNReal
open AvramDividend.Classical
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
  obtain ⟨t, ht⟩ : ∃ t : ℝ≥0, (t : ℝ≥0∞) = ρ := ⟨ρ.toNNReal, ENNReal.coe_toNNReal hρfinite⟩
  rw [AvramDividend.Classical.nextRecord_upclock_eq_add_shifted_inf X b ε hε u ω hu hAt, ← hρ, ← ht,
    ← ENNReal.coe_add, ENNReal.coe_toReal, ENNReal.coe_toReal]
  exact AvramDividend.Classical.discounted_dividend_weight_time_shift q u t
