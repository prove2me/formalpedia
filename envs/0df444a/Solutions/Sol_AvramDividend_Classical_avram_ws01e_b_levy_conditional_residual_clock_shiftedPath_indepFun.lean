-- Prove2me | solution 1 for AvramDividend.Classical.avram_ws01e_b_levy_conditional_residual_clock_shiftedPath_indepFun
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-27T23:52:55.540802+00:00
-- url     : https://prove2.me/submissions/8ab7badc-0656-4dde-95f8-c4c4c9d80d8c

import Mathlib.Probability.ConditionalProbability
import Mathlib.Probability.Independence.Basic
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_ws01e_b_levy_residual_clock_freshPath_rectangle

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
    (hPos : (P.prod Q) {z : Ω × Θ | τ z.1 < e z.2} ≠ 0) :
    IndepFun
      (fun z : Ω × Θ => (e z.2 : ℝ) - (τ z.1 : ℝ))
      (fun z : Ω × Θ => fun s : ℝ≥0 =>
        X.X (τ z.1 + s) z.1 - X.X (τ z.1) z.1)
      ((P.prod Q)[|{z : Ω × Θ | τ z.1 < e z.2}]) := by
  haveI : IsProbabilityMeasure ((P.prod Q)[|{z : Ω × Θ | τ z.1 < e z.2}]) :=
    cond_isProbabilityMeasure hPos
  have hrect := fun A hA B hB =>
    AvramDividend.Classical.avram_ws01e_b_levy_residual_clock_freshPath_rectangle X τ hτ hStop Q e he
      A hA B hB
  rw [indepFun_iff_measure_inter_preimage_eq_mul]
  intro A B hA hB
  have hY : (P.prod Q)[|{z : Ω × Θ | τ z.1 < e z.2}]
      ((fun z : Ω × Θ => fun s : ℝ≥0 => X.X (τ z.1 + s) z.1 - X.X (τ z.1) z.1) ⁻¹' B) =
      P {ω : Ω | (fun s : ℝ≥0 => X.X s ω) ∈ B} := by
    have h := hrect univ MeasurableSet.univ B hB
    have h1 : {z : Ω × Θ | ((e z.2 : ℝ) - (τ z.1 : ℝ)) ∈ (univ : Set ℝ)} = univ := by
      ext z; simp
    rw [h1, measure_univ, one_mul] at h
    rw [← h]
    congr 1
    ext z; simp
  rw [hY]
  exact hrect A hA B hB
