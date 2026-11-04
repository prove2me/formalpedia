-- Prove2me | solution 1 for AvramDividend.Classical.avram_p2_f_weighted_original_horizon_mono_lintegral
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T17:36:16.449286+00:00
-- url     : https://prove2.me/submissions/b4971e11-afa2-4169-b334-8ca3aebcc095

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal

/-- Extending the observation horizon can only increase an original
intrinsic marked jump expectation with arbitrary nonnegative ENNReal weight. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (s T U : ℝ≥0) (hTU : T ≤ U) (B : Set ℝ)
    (H : Ω → ℝ≥0∞) :
    (∫⁻ ω, H ω * ((Measure.count.restrict {u : ℝ≥0 |
      0 < u ∧ X.X u ω -
        Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
      (fun u : ℝ≥0 => (u,
        X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
      (Ioc s (s + T) ×ˢ B) ∂P) ≤
    (∫⁻ ω, H ω * ((Measure.count.restrict {u : ℝ≥0 |
      0 < u ∧ X.X u ω -
        Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
      (fun u : ℝ≥0 => (u,
        X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
      (Ioc s (s + U) ×ˢ B) ∂P) := by
  have hIoc : Ioc s (s + T) ⊆ Ioc s (s + U) := by
    intro u hu
    refine ⟨hu.1, le_trans hu.2 ?_⟩
    simpa only [add_comm s T, add_comm s U] using
      (add_le_add_left hTU s)
  apply MeasureTheory.lintegral_mono
  intro ω
  exact mul_le_mul_of_nonneg_left
    (measure_mono (Set.prod_mono hIoc Subset.rfl)) zero_le
