-- Prove2me | solution 1 for AvramDividend.Classical.avram_ws01e_b_true_memoryless_residual_clock_freshPath_product_law
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-28T01:04:17.271508+00:00
-- url     : https://prove2.me/submissions/2775ae9e-d78b-4b53-9ed0-d28df6573b30

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_ws01e_b_conditional_residual_real_clock_law_eq_fresh
import Theorems.Thm_AvramDividend_Classical_avram_ws01e_b_levy_conditional_joint_residual_freshPath_product_law

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
    (hZero : discount 0 = 1)
    (hPos : (P.prod Q) {z : Ω × Θ | τ z.1 < e z.2} ≠ 0) :
    Measure.map
      (fun z : Ω × Θ =>
        ((e z.2 : ℝ) - (τ z.1 : ℝ),
          fun s : ℝ≥0 =>
            X.X (τ z.1 + s) z.1 - X.X (τ z.1) z.1))
      ((P.prod Q)[|{z : Ω × Θ | τ z.1 < e z.2}]) =
    (Measure.map (fun η : Θ => (e η : ℝ)) Q).prod
      (Measure.map (fun ω : Ω => fun s : ℝ≥0 => X.X s ω) P) := by
  have hClock :=
    avram_ws01e_b_conditional_residual_real_clock_law_eq_fresh
      P Q τ hτ (fun _ : Ω => (0 : ℝ)) measurable_const
      (indepFun_const_right τ (0 : ℝ))
      e he discount hd hTail factor hShift hZero hPos
  have hJoint :=
    avram_ws01e_b_levy_conditional_joint_residual_freshPath_product_law
      X τ hτ hStop Q e he hPos
  rw [hClock] at hJoint
  exact hJoint
