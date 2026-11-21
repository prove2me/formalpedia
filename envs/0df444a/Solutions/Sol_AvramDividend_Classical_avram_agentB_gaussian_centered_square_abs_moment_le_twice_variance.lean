-- Prove2me | solution 1 for AvramDividend.Classical.avram_agentB_gaussian_centered_square_abs_moment_le_twice_variance
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-20T12:34:26.72221+00:00
-- url     : https://prove2.me/submissions/d6e5809d-090c-4be0-bdab-af99fdb6d878

import Mathlib
import Definitions.Def_AvramDividend_Classical_DividendStrategy
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section
set_option autoImplicit false
/-- Centred Gaussian second-Hermite absolute cell energy is at most
twice the real second moment on a probability space. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (Y : Ω → ℝ) (v : ℝ) (hv : 0 ≤ v)
    (hY : Integrable (fun ω => (Y ω)^2) P)
    (hMean : (∫ ω, (Y ω)^2 ∂P) = v) :
    Integrable (fun ω => |(Y ω)^2 - v|) P ∧
    (∫ ω, |(Y ω)^2 - v| ∂P) ≤ 2 * v := by
  have hDiff : Integrable (fun ω => (Y ω)^2 - v) P :=
    hY.sub (integrable_const v)
  have hAbs : Integrable (fun ω => |(Y ω)^2 - v|) P := hDiff.abs
  have hBound (ω : Ω) : |(Y ω)^2 - v| ≤ (Y ω)^2 + v := by
    calc
      |(Y ω)^2 - v| ≤ |(Y ω)^2| + |v| := abs_sub _ _
      _ = (Y ω)^2 + v := by rw [abs_of_nonneg (sq_nonneg _), abs_of_nonneg hv]
  have hUpper : Integrable (fun ω => (Y ω)^2 + v) P :=
    hY.add (integrable_const v)
  have hI := integral_mono hAbs hUpper hBound
  rw [integral_add hY (integrable_const v), integral_const, hMean] at hI
  refine ⟨hAbs, ?_⟩
  simpa [two_mul] using hI
