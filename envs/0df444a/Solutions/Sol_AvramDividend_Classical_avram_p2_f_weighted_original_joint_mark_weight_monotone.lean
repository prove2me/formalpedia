-- Prove2me | solution 1 for AvramDividend.Classical.avram_p2_f_weighted_original_joint_mark_weight_monotone
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T18:27:26.950011+00:00
-- url     : https://prove2.me/submissions/7a7b8708-b684-4670-a2d1-9f3bc4388903

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal

/-- Increasing both original intrinsic mark bands and nonnegative path
weights increases the true weighted expected count, even with infinities. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (s T : ℝ≥0) (B : ℕ → Set ℝ)
    (hB : Monotone B)
    (H : ℕ → Ω → ℝ≥0∞)
    (hH : ∀ i j, i ≤ j → ∀ ω, H i ω ≤ H j ω) :
    Monotone (fun n : ℕ =>
      (∫⁻ ω, H n ω * ((Measure.count.restrict {u : ℝ≥0 |
      0 < u ∧ X.X u ω -
        Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
      (fun u : ℝ≥0 => (u,
        X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
      (Ioc s (s + T) ×ˢ (B n)) ∂P)) := by
  intro i j hij
  apply MeasureTheory.lintegral_mono
  intro ω
  calc
    H i ω * ((Measure.count.restrict {u : ℝ≥0 |
      0 < u ∧ X.X u ω -
        Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
      (fun u : ℝ≥0 => (u,
        X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
      (Ioc s (s + T) ×ˢ (B i)) ≤
        H j ω * ((Measure.count.restrict {u : ℝ≥0 |
      0 < u ∧ X.X u ω -
        Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
      (fun u : ℝ≥0 => (u,
        X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
      (Ioc s (s + T) ×ˢ (B i)) := by
          exact mul_le_mul_of_nonneg_right (hH i j hij ω) zero_le
    _ ≤ H j ω * ((Measure.count.restrict {u : ℝ≥0 |
      0 < u ∧ X.X u ω -
        Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
      (fun u : ℝ≥0 => (u,
        X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
      (Ioc s (s + T) ×ˢ (B j)) := by
          exact mul_le_mul_of_nonneg_left
            (measure_mono (Set.prod_mono Subset.rfl (hB hij))) zero_le
