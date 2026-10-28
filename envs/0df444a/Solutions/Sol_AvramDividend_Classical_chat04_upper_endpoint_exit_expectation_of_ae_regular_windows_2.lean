-- Prove2me | solution 2 for AvramDividend.Classical.chat04_upper_endpoint_exit_expectation_of_ae_regular_windows
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-25T09:47:02.720613+00:00
-- url     : https://prove2.me/submissions/191a7bf6-07cf-4e76-ac85-bf886490f9cf

import Definitions.Def_AvramDividend_Classical_TwoSidedExit
import Theorems.Thm_AvramDividend_Classical_chat04_upper_endpoint_two_sided_exit_expectation_one
import Theorems.Thm_AvramDividend_Classical_chat04_up_exit_time_zero_of_positive_near_zero
import Theorems.Thm_AvramDividend_Classical_chat04_down_exit_time_pos_of_initial_safe_window
import Mathlib.MeasureTheory.Integral.Lebesgue.Add

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
    (hplus : ∀ᵐ ω ∂P,
      ∀ ε : ℝ≥0, 0 < ε →
        ∃ t : ℝ≥0, t < ε ∧ 0 < X.X t ω)
    (hsafe : ∀ᵐ ω ∂P,
      ∃ ε : ℝ≥0, 0 < ε ∧
        ∀ t : ℝ≥0, t < ε → -a ≤ X.X t ω) :
    twoSidedExitExpectation X q a a = 1 := by
  apply chat04_upper_endpoint_two_sided_exit_expectation_one X q a
  · filter_upwards [hplus] with ω hω
    exact chat04_up_exit_time_zero_of_positive_near_zero X ω hω
  · filter_upwards [hsafe] with ω hω
    obtain ⟨ε, hε, hstay⟩ := hω
    exact chat04_down_exit_time_pos_of_initial_safe_window
      X a ω ε hε hstay
