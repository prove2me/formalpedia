-- Prove2me | solution 1 for AvramDividend.Classical.avram_root29_03_exit_finite_reward_split
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-29T09:49:02.960595+00:00
-- url     : https://prove2.me/submissions/45a0e44d-9a6f-40f1-85e4-5d5d5e0b80fc

import Mathlib
import Definitions.Def_AvramDividend_Classical_TwoSidedExit
import Theorems.Thm_AvramDividend_Classical_avram_root29_03_exit_clock_partition_of_finite
import Theorems.Thm_AvramDividend_Classical_chat03_upper_before_lower_passage_event_measurable

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P μ : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (a x : ℝ) (ha : 0 < a) (f : Ω → ℝ≥0∞)
    (hf : Measurable f) :
    (∫⁻ ω, if twoSidedExitUpTime X (a - x) ω < ⊤ ∨
        twoSidedExitDownTime X (-x) ω < ⊤ then f ω else 0 ∂μ) =
    (∫⁻ ω, if twoSidedExitUpTime X (a - x) ω <
        twoSidedExitDownTime X (-x) ω then f ω else 0 ∂μ) +
    (∫⁻ ω, if twoSidedExitDownTime X (-x) ω <
        twoSidedExitUpTime X (a - x) ω then f ω else 0 ∂μ) := by
  have hA := AvramDividend.Classical.chat03_upper_before_lower_passage_event_measurable X (-x) (a - x)
  have hm : Measurable (fun ω => if twoSidedExitUpTime X (a - x) ω <
        twoSidedExitDownTime X (-x) ω then f ω else 0) :=
    Measurable.ite hA hf measurable_const
  rw [← lintegral_add_left hm]
  apply lintegral_congr
  intro ω
  have hp := AvramDividend.Classical.avram_root29_03_exit_clock_partition_of_finite X a x ha ω
  by_cases h1 : twoSidedExitUpTime X (a - x) ω < twoSidedExitDownTime X (-x) ω
  · have h2 : ¬ twoSidedExitDownTime X (-x) ω < twoSidedExitUpTime X (a - x) ω := lt_asymm h1
    rw [if_pos (hp.mp (Or.inl h1)), if_pos h1, if_neg h2, add_zero]
  · by_cases h2 : twoSidedExitDownTime X (-x) ω < twoSidedExitUpTime X (a - x) ω
    · rw [if_pos (hp.mp (Or.inr h2)), if_neg h1, if_pos h2, zero_add]
    · have : ¬ (twoSidedExitUpTime X (a - x) ω < ⊤ ∨ twoSidedExitDownTime X (-x) ω < ⊤) :=
        fun h => (hp.mpr h).elim h1 h2
      rw [if_neg this, if_neg h1, if_neg h2, add_zero]
