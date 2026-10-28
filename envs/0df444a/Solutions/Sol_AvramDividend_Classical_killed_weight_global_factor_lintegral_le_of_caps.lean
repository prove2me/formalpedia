-- Prove2me | solution 1 for AvramDividend.Classical.killed_weight_global_factor_lintegral_le_of_caps
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-26T09:47:36.233582+00:00
-- url     : https://prove2.me/submissions/47e26746-e441-45d6-a0f4-60c4d3b1454d

import Mathlib.MeasureTheory.Integral.Lebesgue.Add
import Theorems.Thm_AvramDividend_Classical_killed_weight_global_lintegral_le_of_uniform_caps

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory
open scoped ENNReal

/-- A uniform cap bound persists after multiplying a killed reward by a fixed factor. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    (P : Measure Ω) (T : Ω → ℝ≥0∞) (hT : Measurable T)
    (weight : Ω → ℝ≥0∞) (hw : Measurable weight)
    (hzero : ∀ ω, T ω = ⊤ → weight ω = 0)
    (factor bound : ℝ≥0∞)
    (hbound : ∀ n : ℕ, factor *
      (∫⁻ ω, if T ω ≤ (n : ℝ≥0∞) then weight ω else 0 ∂P) ≤ bound) :
    factor * (∫⁻ ω, weight ω ∂P) ≤ bound := by
  have hw' : Measurable (fun ω => factor * weight ω) :=
    measurable_const.mul hw
  have hz' : ∀ ω, T ω = ⊤ → factor * weight ω = 0 := by
    intro ω hω
    simp [hzero ω hω]
  have hc (n : ℕ) :
      (∫⁻ ω, if T ω ≤ (n : ℝ≥0∞) then
        factor * weight ω else 0 ∂P) ≤ bound := by
    have hmeas : Measurable
        (fun ω => if T ω ≤ (n : ℝ≥0∞) then weight ω else 0) :=
      Measurable.ite (measurableSet_le hT measurable_const)
        hw measurable_const
    have h := hbound n
    rw [← lintegral_const_mul factor hmeas] at h
    simpa only [mul_ite, mul_zero] using h
  have hmain := killed_weight_global_lintegral_le_of_uniform_caps
    P T hT (fun ω => factor * weight ω) hw' hz' bound hc
  rwa [lintegral_const_mul factor hw] at hmain
