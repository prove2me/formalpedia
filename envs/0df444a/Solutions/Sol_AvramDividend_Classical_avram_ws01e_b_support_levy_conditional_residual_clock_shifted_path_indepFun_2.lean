-- Prove2me | solution 2 for AvramDividend.Classical.avram_ws01e_b_support_levy_conditional_residual_clock_shifted_path_indepFun
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-27T23:50:12.136176+00:00
-- url     : https://prove2.me/submissions/446f216d-502f-490d-9a7c-956c6af41080

import Mathlib.MeasureTheory.MeasurableSpace.Constructions
import Mathlib.Probability.ConditionalProbability
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_isStoppingTime_withTop_of_le_events
import Theorems.Thm_AvramDividend_Classical_levy_finiteStopping_stoppedFuturePath_measurable
import Theorems.Thm_AvramDividend_Classical_levy_finiteStopping_clock_indep_shiftedPath
import Theorems.Thm_AvramDividend_Classical_avram_ws01e_b_conditional_residual_clock_future_indepFun

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal

theorem solution
    {Ω Θ : Type*} [mΩ : MeasurableSpace Ω] [MeasurableSpace Θ]
    {P : Measure Ω} [IsProbabilityMeasure P]
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (τ : Ω → ℝ≥0) (hτ : Measurable τ)
    (hStop : ∀ s : ℝ≥0, MeasurableSet[𝓕 s] {ω : Ω | τ ω ≤ s})
    (Q : Measure Θ) [IsProbabilityMeasure Q]
    (e : Θ → ℝ≥0) (he : Measurable e)
    (discount : ℝ≥0 → ℝ≥0∞) (hd : Measurable discount)
    (hTail : ∀ a : ℝ≥0, Q {η : Θ | a < e η} = discount a)
    (factor : ℝ≥0 → ℝ≥0∞)
    (hShift : ∀ a t : ℝ≥0, discount (a + t) = factor t * discount a)
    (hPos : (P.prod Q) {z : Ω × Θ | τ z.1 < e z.2} ≠ 0) :
    IndepFun
      (fun z : Ω × Θ => (e z.2 : ℝ) - (τ z.1 : ℝ))
      (fun z : Ω × Θ => fun s : ℝ≥0 =>
        X.X (τ z.1 + s) z.1 - X.X (τ z.1) z.1)
      ((P.prod Q)[|{z : Ω × Θ | τ z.1 < e z.2}]) := by
  have hStop' : IsStoppingTime 𝓕
      (fun ω => (τ ω : WithTop ℝ≥0)) :=
    isStoppingTime_withTop_of_le_events τ hStop
  have hFuture : Measurable (fun ω : Ω => fun s : ℝ≥0 =>
      X.X (τ ω + s) ω - X.X (τ ω) ω) :=
    levy_finiteStopping_stoppedFuturePath_measurable X τ hStop'
  have hInd : IndepFun τ
      (fun ω : Ω => fun s : ℝ≥0 =>
        X.X (τ ω + s) ω - X.X (τ ω) ω) P :=
    levy_finiteStopping_clock_indep_shiftedPath X τ hStop
  exact avram_ws01e_b_conditional_residual_clock_future_indepFun
    P Q τ hτ _ hFuture hInd e he discount hd hTail factor hShift hPos
