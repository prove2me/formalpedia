-- Prove2me | solution 1 for AvramDividend.Classical.avram_ws01e_b_conditional_freshPath_joint_lintegral_regeneration
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-28T00:35:45.843505+00:00
-- url     : https://prove2.me/submissions/2f18071d-d015-4b5d-99b2-24eee5ebc84b

import Mathlib.Probability.ConditionalProbability
import Mathlib.MeasureTheory.Integral.Lebesgue.Map
import Mathlib.MeasureTheory.MeasurableSpace.Constructions
import Theorems.Thm_AvramDividend_Classical_avram_ws01e_b_levy_conditional_joint_residual_freshPath_product_law
import Theorems.Thm_AvramDividend_Classical_levy_finiteStopping_stoppedFuturePath_measurable
import Theorems.Thm_AvramDividend_Classical_isStoppingTime_withTop_of_le_events

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
    (hPos : (P.prod Q) {z : Ω × Θ | τ z.1 < e z.2} ≠ 0)
    (G : ℝ × (ℝ≥0 → ℝ) → ℝ≥0∞) (hG : Measurable G) :
    (∫⁻ z : Ω × Θ,
      G ((e z.2 : ℝ) - (τ z.1 : ℝ),
          fun s : ℝ≥0 => X.X (τ z.1 + s) z.1 - X.X (τ z.1) z.1)
        ∂((P.prod Q)[|{z : Ω × Θ | τ z.1 < e z.2}])) =
    (∫⁻ y : ℝ × (ℝ≥0 → ℝ), G y
      ∂(Measure.map (fun z : Ω × Θ => (e z.2 : ℝ) - (τ z.1 : ℝ))
         ((P.prod Q)[|{z : Ω × Θ | τ z.1 < e z.2}])).prod
       (Measure.map (fun ω : Ω => fun s : ℝ≥0 => X.X s ω) P)) := by
  have hFuture : Measurable
      (fun ω : Ω => fun s : ℝ≥0 =>
        X.X (τ ω + s) ω - X.X (τ ω) ω) :=
    levy_finiteStopping_stoppedFuturePath_measurable X τ
      (isStoppingTime_withTop_of_le_events τ hStop)
  have hR : Measurable
      (fun z : Ω × Θ => (e z.2 : ℝ) - (τ z.1 : ℝ)) := by
    fun_prop
  have hPair : Measurable
      (fun z : Ω × Θ =>
        ((e z.2 : ℝ) - (τ z.1 : ℝ),
          fun s : ℝ≥0 =>
            X.X (τ z.1 + s) z.1 - X.X (τ z.1) z.1)) :=
    hR.prodMk (hFuture.comp measurable_fst)
  have hLaw :=
    avram_ws01e_b_levy_conditional_joint_residual_freshPath_product_law
      X τ hτ hStop Q e he hPos
  rw [← hLaw]
  exact (lintegral_map hG hPair).symm
