-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave3_04_discounted_deriv_stronglyPredictable
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-30T13:03:56.057161+00:00
-- url     : https://prove2.me/submissions/5b9d8d8b-f3d4-4c35-a80b-529f010cceba

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_wave3_04_strongAdapted_leftContinuous_predictable

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter Set Topology AvramDividend.Classical
open scoped NNReal

/-- Discounted derivative of a strongly predictable real process is itself
strongly predictable for the same original filtration. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {𝓕 : Filtration ℝ≥0 mΩ}
    (Z : ℝ≥0 → Ω → ℝ)
    (hZ : IsStronglyPredictable 𝓕 Z)
    (w : ℝ → ℝ) (q : ℝ) :
    IsStronglyPredictable 𝓕
      (fun t ω => Real.exp (-(q * (t : ℝ))) * deriv w (Z t ω)) := by
  let B : ℝ≥0 → Ω → ℝ :=
    fun t _ => Real.exp (-(q * (t : ℝ)))
  have hBadapt : StronglyAdapted 𝓕 B := by
    intro t
    exact stronglyMeasurable_const
  have hBcont : ∀ ω (t : ℝ≥0),
      ContinuousWithinAt (fun s => B s ω) (Iic t) t := by
    intro ω t
    dsimp [B]
    fun_prop
  have hBpred : IsStronglyPredictable 𝓕 B :=
    avram_wave3_04_strongAdapted_leftContinuous_predictable hBadapt hBcont
  have hDeriv : IsStronglyPredictable 𝓕
      (fun t ω => deriv w (Z t ω)) := by
    change StronglyMeasurable[𝓕.predictable]
      (fun p : ℝ≥0 × Ω => deriv w (Z p.1 p.2))
    letI : MeasurableSpace (ℝ≥0 × Ω) := 𝓕.predictable
    exact ((measurable_deriv w).comp hZ.measurable).stronglyMeasurable
  exact hBpred.mul hDeriv
