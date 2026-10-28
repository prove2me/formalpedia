-- Prove2me | solution 1 for AvramDividend.Classical.chat04_upper_endpoint_exit_expectation_of_ae_regular_windows
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-25T09:46:46.553961+00:00
-- url     : https://prove2.me/submissions/2f6c1c92-cc99-42cb-8caf-ec62988fc92f

import Definitions.Def_AvramDividend_Classical_TwoSidedExit
import Theorems.Thm_AvramDividend_Classical_chat04_upper_endpoint_two_sided_exit_expectation_one
import Theorems.Thm_AvramDividend_Classical_chat04_up_exit_time_zero_of_positive_near_zero
import Theorems.Thm_AvramDividend_Classical_chat04_down_exit_time_pos_of_initial_safe_window
import Mathlib.MeasureTheory.Integral.Lebesgue.Add

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
  refine AvramDividend.Classical.chat04_upper_endpoint_two_sided_exit_expectation_one X q a ?_ ?_
  · filter_upwards [hplus] with ω hω
    exact AvramDividend.Classical.chat04_up_exit_time_zero_of_positive_near_zero X ω hω
  · filter_upwards [hsafe] with ω ⟨ε, hε, hω⟩
    exact AvramDividend.Classical.chat04_down_exit_time_pos_of_initial_safe_window X a ω ε hε hω
