-- Prove2me | solution 1 for AvramDividend.Classical.avram_redux18_integrated_count_pgf_sandwich
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-06T17:34:42.528385+00:00
-- url     : https://prove2.me/submissions/363d5866-ae9b-4fc3-bae0-0c71d548d09e

import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Theorems.Thm_AvramDividend_Classical_avram_redux18_count_pgf_pointwise_sandwich
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory
noncomputable section

/-! Integrate the pointwise PGF bounds without assuming the base measure finite. -/
theorem solution
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (N : Ω → ℕ) (z : ℝ) (hz0 : 0 ≤ z) (hz1 : z ≤ 1)
    (hN : Integrable (fun ω => (N ω : ℝ)) μ)
    (hZ : Integrable (fun ω => z ^ (N ω)) μ)
    (hI : Integrable (fun ω => if N ω = 0 then (1 : ℝ) else z) μ) :
    (∫ ω, (1 : ℝ) - (1 - z) * (N ω : ℝ) ∂μ) ≤
      (∫ ω, z ^ (N ω) ∂μ) ∧
    (∫ ω, z ^ (N ω) ∂μ) ≤
      (∫ ω, if N ω = 0 then (1 : ℝ) else z ∂μ) := by
  constructor
  · by_cases hL :
        Integrable (fun ω => (1 : ℝ) - (1 - z) * (N ω : ℝ)) μ
    · exact integral_mono hL hZ (fun ω =>
        (AvramDividend.Classical.avram_redux18_count_pgf_pointwise_sandwich
          z hz0 hz1 (N ω)).1)
    · rw [integral_undef hL]
      exact integral_nonneg (fun ω => pow_nonneg hz0 (N ω))
  · exact integral_mono hZ hI (fun ω =>
      (AvramDividend.Classical.avram_redux18_count_pgf_pointwise_sandwich
        z hz0 hz1 (N ω)).2)
