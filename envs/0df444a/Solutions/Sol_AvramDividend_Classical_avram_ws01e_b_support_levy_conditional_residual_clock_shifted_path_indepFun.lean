-- Prove2me | solution 1 for AvramDividend.Classical.avram_ws01e_b_support_levy_conditional_residual_clock_shifted_path_indepFun
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-27T23:49:20.399062+00:00
-- url     : https://prove2.me/submissions/261640a5-fa79-4e68-b404-77ca96810b26

import Mathlib.MeasureTheory.MeasurableSpace.Constructions
import Mathlib.Probability.ConditionalProbability
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_chat04_levy_joint_time_state_measurable
import Theorems.Thm_AvramDividend_Classical_levy_finiteStopping_clock_indep_shiftedPath
import Theorems.Thm_AvramDividend_Classical_avram_ws01e_b_conditional_residual_clock_future_indepFun

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
  have hJ := AvramDividend.Classical.chat04_levy_joint_time_state_measurable X
  have hm1 : Measurable (fun ω : Ω => fun s : ℝ≥0 => X.X (τ ω + s) ω - X.X (τ ω) ω) := by
    refine measurable_pi_lambda _ (fun s => ?_)
    exact (hJ.comp ((hτ.add_const s).prodMk measurable_id)).sub
      (hJ.comp (hτ.prodMk measurable_id))
  exact AvramDividend.Classical.avram_ws01e_b_conditional_residual_clock_future_indepFun
    P Q τ hτ (fun ω : Ω => fun s : ℝ≥0 => X.X (τ ω + s) ω - X.X (τ ω) ω) hm1
    (AvramDividend.Classical.levy_finiteStopping_clock_indep_shiftedPath X τ hStop)
    e he discount hd hTail factor hShift hPos
