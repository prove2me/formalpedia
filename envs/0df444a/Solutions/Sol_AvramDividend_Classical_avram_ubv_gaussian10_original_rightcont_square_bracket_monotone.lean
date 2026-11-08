-- Prove2me | solution 1 for AvramDividend.Classical.avram_ubv_gaussian10_original_rightcont_square_bracket_monotone
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-07T11:22:52.280041+00:00
-- url     : https://prove2.me/submissions/9f12abf4-35a6-44db-bec4-2bca79171076

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- At any fixed sample point of the original process, finite quadratic energy
makes the stopped Brownian bracket nondecreasing in the physical time clock. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (H : ℝ≥0 × Ω → ℝ) (μtime : Measure ℝ≥0)
    (hInt : ∀ ω b, IntegrableOn
      (fun t : ℝ≥0 => (H (t, ω)) ^ 2)
      (Ioc (0 : ℝ≥0) b) μtime) :
    ∀ ω, Monotone (fun b : ℝ≥0 =>
      ∫ t in Ioc (0 : ℝ≥0) b, (H (t, ω)) ^ 2 ∂μtime) := by
  intro ω a b hab
  apply setIntegral_mono_set (hInt ω b)
  · filter_upwards [] with t
    exact sq_nonneg (H (t, ω))
  · filter_upwards [] with t ht
    exact ⟨ht.1, ht.2.trans hab⟩
