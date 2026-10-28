-- Prove2me | solution 2 for AvramDividend.Classical.avram_ws01e_b_support_firstRecord_uncensored_discountedFutureReward_factor
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-28T00:23:56.740608+00:00
-- url     : https://prove2.me/submissions/78d0c479-bc16-4773-a8e8-ffcba0f497cd

import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Mathlib.Probability.Process.Stopping
import Definitions.Def_AvramDividend_Classical_TwoSidedExit
import Theorems.Thm_AvramDividend_Classical_isStoppingTime_withTop_of_le_events
import Theorems.Thm_AvramDividend_Classical_firstRecord_truncation_stopping_rightCont
import Theorems.Thm_AvramDividend_Classical_firstRecord_truncation_clock_measurable
import Theorems.Thm_AvramDividend_Classical_avram_ws01e_b_support_firstRecord_strict_upcrossing_stoppedHistory
import Theorems.Thm_AvramDividend_Classical_levy_rightCont_finiteStopping_discountedFutureReward_factor

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (b : ℝ) (N : ℝ≥0)
    (discount : ℝ≥0 → ℝ≥0∞) (hd : Measurable discount)
    (reward : (ℝ≥0 → ℝ) → ℝ≥0∞) (hr : Measurable reward) :
    (let τ : Ω → ℝ≥0 := fun ω =>
       (min (twoSidedExitUpTime X b ω) (N : ℝ≥0∞)).toNNReal
     let A : Set Ω := {ω : Ω | twoSidedExitUpTime X b ω < (N : ℝ≥0∞)}
     (∫⁻ ω, if ω ∈ A then discount (τ ω) *
       reward (fun t : ℝ≥0 =>
         X.X (τ ω + t) ω - X.X (τ ω) ω) else 0 ∂P) =
       (∫⁻ ω, if ω ∈ A then discount (τ ω) else 0 ∂P) *
         (∫⁻ ω, reward (fun t : ℝ≥0 => X.X t ω) ∂P)) := by
  intro τ A
  have hA := avram_ws01e_b_support_firstRecord_strict_upcrossing_stoppedHistory X b N
  have hAfine : MeasurableSet A :=
    (isStoppingTime_withTop_of_le_events _ (firstRecord_truncation_stopping_rightCont X b N)).measurableSpace_le _ hA
  convert levy_rightCont_finiteStopping_discountedFutureReward_factor X τ
    (firstRecord_truncation_stopping_rightCont X b N) A hA hAfine
    (firstRecord_truncation_clock_measurable X b N) discount hd reward hr
