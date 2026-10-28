-- Prove2me | solution 1 for AvramDividend.Classical.chat04_upper_endpoint_stopped_scale_of_ae_up_clock
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-25T10:22:21.112572+00:00
-- url     : https://prove2.me/submissions/2b345192-c490-4c85-9356-820d6fad81a0

import Definitions.Def_AvramDividend_Classical_TwoSidedExit
import Theorems.Thm_AvramDividend_Classical_chat04_down_exit_time_pos_ae_of_positive_barrier
import Theorems.Thm_AvramDividend_Classical_chat04_upper_endpoint_two_sided_exit_expectation_one
import Mathlib.Data.ENNReal.Basic
import Mathlib.MeasureTheory.MeasurableSpace.Defs

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

/-! The exact upper-endpoint stopped-scale identity follows from the up-clock alone. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q a : ℝ) (ha : 0 < a)
    (W : ℝ → ℝ)
    (hup0 : ∀ᵐ ω ∂P, twoSidedExitUpTime X 0 ω = 0) :
    twoSidedExitExpectation X q a a * ENNReal.ofReal (W a) =
      ENNReal.ofReal (W a) := by
  have hdownpos : ∀ᵐ ω ∂P,
      0 < twoSidedExitDownTime X (-a) ω :=
    chat04_down_exit_time_pos_ae_of_positive_barrier X a ha
  rw [chat04_upper_endpoint_two_sided_exit_expectation_one X q a hup0 hdownpos]
  simp
