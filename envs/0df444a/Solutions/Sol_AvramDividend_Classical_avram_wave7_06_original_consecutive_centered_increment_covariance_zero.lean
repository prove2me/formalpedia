-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave7_06_original_consecutive_centered_increment_covariance_zero
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-02T17:53:04.868276+00:00
-- url     : https://prove2.me/submissions/d563231a-0e01-4234-9b66-6b6f3937df26

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave7_06_original_successive_future_increments_indepFun

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter Set Topology ProbabilityTheory AvramDividend.Classical
open scoped NNReal ENNReal

/-- Exact zero covariance of consecutive original-source increments, centred by their own means. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (s u v : ℝ≥0)
    (hFirst : Integrable (fun ω => X.X (s + u) ω - X.X s ω) P)
    (hSecond : Integrable (fun ω =>
      X.X (s + u + v) ω - X.X (s + u) ω) P) :
    (∫ ω,
      ((X.X (s + u) ω - X.X s ω) -
        (∫ η, X.X (s + u) η - X.X s η ∂P)) *
      ((X.X (s + u + v) ω - X.X (s + u) ω) -
        (∫ η, X.X (s + u + v) η - X.X (s + u) η ∂P)) ∂P) = 0 := by
  letI : IsProbabilityMeasure P := X.isProbability
  let A : Ω → ℝ := fun ω => X.X (s + u) ω - X.X s ω
  let B : Ω → ℝ := fun ω => X.X (s + u + v) ω - X.X (s + u) ω
  let a : ℝ := ∫ ω, A ω ∂P
  let b : ℝ := ∫ ω, B ω ∂P
  have hA : Integrable A P := hFirst
  have hB : Integrable B P := hSecond
  have hAc : Integrable (fun ω => A ω - a) P :=
    hA.sub (integrable_const a)
  have hBc : Integrable (fun ω => B ω - b) P :=
    hB.sub (integrable_const b)
  have hIndep : IndepFun A B P :=
    avram_wave7_06_original_successive_future_increments_indepFun
      X s u v
  have hPhi : Measurable (fun y : ℝ => y - a) :=
    measurable_id.sub measurable_const
  have hPsi : Measurable (fun y : ℝ => y - b) :=
    measurable_id.sub measurable_const
  have hCentered : IndepFun
      (fun ω => A ω - a) (fun ω => B ω - b) P := by
    simpa only [Function.comp_def] using hIndep.comp hPhi hPsi
  have hZa : (∫ ω, A ω - a ∂P) = 0 := by
    rw [integral_sub hA (integrable_const a)]
    simp [a]
  have hZb : (∫ ω, B ω - b ∂P) = 0 := by
    rw [integral_sub hB (integrable_const b)]
    simp [b]
  have hFactor := hCentered.integral_mul_eq_mul_integral
    hAc.aestronglyMeasurable hBc.aestronglyMeasurable
  change (∫ ω, (A ω - a) * (B ω - b) ∂P) =
    (∫ ω, A ω - a ∂P) * (∫ ω, B ω - b ∂P) at hFactor
  rw [hZa, hZb, zero_mul] at hFactor
  exact hFactor
