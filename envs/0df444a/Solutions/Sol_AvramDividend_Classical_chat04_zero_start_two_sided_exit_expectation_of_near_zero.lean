-- Prove2me | solution 1 for AvramDividend.Classical.chat04_zero_start_two_sided_exit_expectation_of_near_zero
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-25T09:27:55.081748+00:00
-- url     : https://prove2.me/submissions/6314d626-7956-426e-94bb-4e25cddf2ae5

import Mathlib.MeasureTheory.Integral.Lebesgue.Add
import Mathlib.Analysis.Complex.Exponential
import Definitions.Def_AvramDividend_Classical_TwoSidedExit
import Theorems.Thm_AvramDividend_Classical_chat04_down_exit_time_zero_of_negative_near_zero

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q a : ℝ)
    (hnear : ∀ᵐ ω ∂P,
      ∀ ε : ℝ≥0, 0 < ε →
        ∃ s : ℝ≥0, s < ε ∧ X.X s ω < 0) :
    twoSidedExitExpectation X q a 0 = 0 := by
  have hzero : ∀ᵐ ω ∂P,
      (if twoSidedExitUpTime X (a - 0) ω <
          twoSidedExitDownTime X (-0) ω then
        ENNReal.ofReal
          (Real.exp (-(q * ENNReal.toReal
            (twoSidedExitUpTime X (a - 0) ω))))
       else 0) = 0 := by
    filter_upwards [hnear] with ω hω
    have hdown : twoSidedExitDownTime X (-0) ω = 0 := by
      change (⨅ (t : ℝ≥0) (_ : X.X t ω < -(0 : ℝ)),
        (t : ℝ≥0∞)) = 0
      simpa using
        (chat04_down_exit_time_zero_of_negative_near_zero X ω hω)
    rw [hdown]
    have hn : ¬ (twoSidedExitUpTime X (a - 0) ω <
        (0 : ℝ≥0∞)) := not_lt_of_ge bot_le
    simp [hn]
  unfold twoSidedExitExpectation
  calc
    _ = (∫⁻ _ : Ω, (0 : ℝ≥0∞) ∂P) := lintegral_congr_ae hzero
    _ = 0 := by simp
