-- Prove2me | solution 1 for AvramDividend.Classical.avram_redux18_integrated_factorial_pgf_remainder
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-06T17:57:54.587216+00:00
-- url     : https://prove2.me/submissions/7d942a16-d2e2-423e-a625-385e423bc5da

import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Theorems.Thm_AvramDividend_Classical_avram_redux18_pgf_factorial_remainder
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory
noncomputable section

/-! The second factorial count moment controls the integrated PGF remainder. -/
theorem solution
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsFiniteMeasure μ]
    (N : Ω → ℕ) (z : ℝ) (hz0 : 0 ≤ z) (hz1 : z ≤ 1)
    (hN : Integrable (fun ω => (N ω : ℝ)) μ)
    (hZ : Integrable (fun ω => z ^ (N ω)) μ)
    (hFac : Integrable (fun ω =>
      (N ω : ℝ) * ((N ω : ℝ) - 1)) μ) :
    0 ≤ ∫ ω, (z ^ (N ω) - (1 - (1 - z) * (N ω : ℝ))) ∂μ ∧
    2 * (∫ ω, (z ^ (N ω) - (1 - (1 - z) * (N ω : ℝ))) ∂μ) ≤
      ∫ ω, ((1 - z) ^ 2 * (N ω : ℝ) * ((N ω : ℝ) - 1)) ∂μ := by
  let E : Ω → ℝ := fun ω => z ^ (N ω) - (1 - (1 - z) * (N ω : ℝ))
  let C : Ω → ℝ := fun ω => (1 - z) ^ 2 * (N ω : ℝ) * ((N ω : ℝ) - 1)
  have hL : Integrable (fun ω => 1 - (1 - z) * (N ω : ℝ)) μ :=
    (integrable_const (1 : ℝ)).sub (hN.const_mul (1 - z))
  have hE : Integrable E μ := hZ.sub hL
  have hC : Integrable C μ := by
    simpa only [C, mul_assoc] using (hFac.const_mul ((1 - z) ^ 2))
  have hB (ω : Ω) : 0 ≤ E ω ∧ 2 * E ω ≤ C ω := by
    exact AvramDividend.Classical.avram_redux18_pgf_factorial_remainder
      z hz0 hz1 (N ω)
  change 0 ≤ ∫ ω, E ω ∂μ ∧ 2 * (∫ ω, E ω ∂μ) ≤ ∫ ω, C ω ∂μ
  constructor
  · exact integral_nonneg (fun ω => (hB ω).1)
  · calc
      2 * (∫ ω, E ω ∂μ) = ∫ ω, 2 * E ω ∂μ := by
        rw [integral_const_mul]
      _ ≤ ∫ ω, C ω ∂μ :=
        integral_mono (hE.const_mul 2) hC (fun ω => (hB ω).2)
