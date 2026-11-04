-- Prove2me | solution 1 for AvramDividend.Classical.avram_p2_f_weighted_original_nested_rectangles_lintegral
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T18:40:21.21452+00:00
-- url     : https://prove2.me/submissions/22e8df1f-7838-4a10-a759-f93e67256c43

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal

/-- Rectangular order for the actual intrinsic Lévy jump count:
enlarge time interval, mark band and nonnegative weight simultaneously. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (s0 s1 t0 t1 : ℝ≥0) (hs : s0 ≤ s1) (ht : t1 ≤ t0)
    (B C : Set ℝ) (hBC : B ⊆ C)
    (H K : Ω → ℝ≥0∞) (hHK : ∀ ω, H ω ≤ K ω) :
    (∫⁻ ω, H ω * ((Measure.count.restrict {u : ℝ≥0 |
      0 < u ∧ X.X u ω -
        Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
      (fun u : ℝ≥0 => (u,
        X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
      (Ioc s1 t1 ×ˢ B) ∂P) ≤
    (∫⁻ ω, K ω * ((Measure.count.restrict {u : ℝ≥0 |
      0 < u ∧ X.X u ω -
        Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
      (fun u : ℝ≥0 => (u,
        X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
      (Ioc s0 t0 ×ˢ C) ∂P) := by
  have hTime : Ioc s1 t1 ⊆ Ioc s0 t0 := by
    intro u hu
    exact ⟨lt_of_le_of_lt hs hu.1, le_trans hu.2 ht⟩
  apply MeasureTheory.lintegral_mono
  intro ω
  calc
    H ω * ((Measure.count.restrict {u : ℝ≥0 |
      0 < u ∧ X.X u ω -
        Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
      (fun u : ℝ≥0 => (u,
        X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
      (Ioc s1 t1 ×ˢ B) ≤
        K ω * ((Measure.count.restrict {u : ℝ≥0 |
      0 < u ∧ X.X u ω -
        Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
      (fun u : ℝ≥0 => (u,
        X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
      (Ioc s1 t1 ×ˢ B) :=
          mul_le_mul_of_nonneg_right (hHK ω) zero_le
    _ ≤ K ω * ((Measure.count.restrict {u : ℝ≥0 |
      0 < u ∧ X.X u ω -
        Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
      (fun u : ℝ≥0 => (u,
        X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
      (Ioc s0 t0 ×ˢ C) :=
          mul_le_mul_of_nonneg_left
            (measure_mono (Set.prod_mono hTime hBC)) zero_le
