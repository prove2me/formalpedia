-- Prove2me | solution 1 for AvramDividend.Classical.avram_ws01e_b_levy_residual_clock_freshPath_rectangle
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-27T23:38:13.901002+00:00
-- url     : https://prove2.me/submissions/d45c8251-5cb9-419d-8d9e-9fbbcae8a6e3

import Mathlib.Probability.ConditionalProbability
import Mathlib.MeasureTheory.Constructions.BorelSpace.Real
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_chat04_levy_joint_time_state_measurable
import Theorems.Thm_AvramDividend_Classical_levy_finiteStopping_clock_indep_shiftedPath
import Theorems.Thm_AvramDividend_Classical_levy_finiteStopping_shiftedFuturePath_sameLaw
import Theorems.Thm_AvramDividend_Classical_avram_ws01e_b_conditional_clock_kernel_future_event_factor

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
    (A : Set ℝ) (hA : MeasurableSet A)
    (B : Set (ℝ≥0 → ℝ)) (hB : MeasurableSet B) :
    (P.prod Q)[{z : Ω × Θ |
        ((e z.2 : ℝ) - (τ z.1 : ℝ)) ∈ A ∧
        (fun s : ℝ≥0 => X.X (τ z.1 + s) z.1 - X.X (τ z.1) z.1) ∈ B} |
        {z : Ω × Θ | τ z.1 < e z.2}] =
      (P.prod Q)[{z : Ω × Θ |
          ((e z.2 : ℝ) - (τ z.1 : ℝ)) ∈ A} |
          {z : Ω × Θ | τ z.1 < e z.2}] *
        P {ω : Ω | (fun s : ℝ≥0 => X.X s ω) ∈ B} := by
  have hJ := AvramDividend.Classical.chat04_levy_joint_time_state_measurable X
  have hm1 : Measurable (fun ω : Ω => fun s : ℝ≥0 => X.X (τ ω + s) ω - X.X (τ ω) ω) := by
    refine measurable_pi_lambda _ (fun s => ?_)
    exact (hJ.comp ((hτ.add_const s).prodMk measurable_id)).sub
      (hJ.comp (hτ.prodMk measurable_id))
  have hm2 : Measurable (fun ω : Ω => fun s : ℝ≥0 => X.X s ω) := by
    refine measurable_pi_lambda _ (fun s => ?_)
    exact hJ.comp (measurable_const.prodMk measurable_id)
  have hK : MeasurableSet {z : ℝ≥0 × Θ | ((e z.2 : ℝ) - (z.1 : ℝ)) ∈ A} := by
    have : Measurable (fun z : ℝ≥0 × Θ => (e z.2 : ℝ) - (z.1 : ℝ)) := by fun_prop
    exact this hA
  have hfac := AvramDividend.Classical.avram_ws01e_b_conditional_clock_kernel_future_event_factor
    P Q τ hτ (fun ω : Ω => fun s : ℝ≥0 => X.X (τ ω + s) ω - X.X (τ ω) ω) hm1
    (AvramDividend.Classical.levy_finiteStopping_clock_indep_shiftedPath X τ hStop) e he
    (fun a η => ((e η : ℝ) - (a : ℝ)) ∈ A) hK B hB
  rw [hfac]
  congr 1
  have hlaw := AvramDividend.Classical.levy_finiteStopping_shiftedFuturePath_sameLaw X τ hStop
  have := congrArg (fun μ : Measure (ℝ≥0 → ℝ) => μ B) hlaw
  rw [Measure.map_apply hm1 hB, Measure.map_apply hm2 hB] at this
  exact this
