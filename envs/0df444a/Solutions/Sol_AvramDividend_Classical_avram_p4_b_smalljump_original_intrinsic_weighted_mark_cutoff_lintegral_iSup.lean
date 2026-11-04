-- Prove2me | solution 1 for AvramDividend.Classical.avram_p4_b_smalljump_original_intrinsic_weighted_mark_cutoff_lintegral_iSup
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-04T00:06:13.840304+00:00
-- url     : https://prove2.me/submissions/0d8be7c2-9544-4a5c-838e-c6cc0fdf1604

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p4_b_smalljump_original_intrinsic_marked_count_iUnion_of_monotone_bands

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal

/-- An original intrinsic marked-jump integral with a constant nonnegative
band weight is continuous from below over all increasing Borel cutoffs. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (s t : ℝ≥0) (B : ℕ → Set ℝ) (hMon : Monotone B)
    (hB : ∀ n, MeasurableSet (B n)) (c : ℝ≥0∞) (ω : Ω) :
    (∫⁻ p : ℝ≥0 × ℝ,
      (Ioc s t ×ˢ (⋃ n, B n)).indicator (fun _ => c) p
      ∂((Measure.count.restrict {u : ℝ≥0 |
          0 < u ∧ X.X u ω -
            Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u,
          X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))) =
    ⨆ n, (∫⁻ p : ℝ≥0 × ℝ,
      (Ioc s t ×ˢ B n).indicator (fun _ => c) p
      ∂((Measure.count.restrict {u : ℝ≥0 |
          0 < u ∧ X.X u ω -
            Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u,
          X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))) := by
  let N : Measure (ℝ≥0 × ℝ) :=
    (Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
      (fun u : ℝ≥0 => (u,
        X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u))
  have hUnion : MeasurableSet (⋃ n, B n) :=
    MeasurableSet.iUnion hB
  have hCount : N (Ioc s t ×ˢ (⋃ n, B n)) =
      ⨆ n, N (Ioc s t ×ˢ B n) :=
    avram_p4_b_smalljump_original_intrinsic_marked_count_iUnion_of_monotone_bands
      X s t B hMon ω
  change (∫⁻ p, (Ioc s t ×ˢ (⋃ n, B n)).indicator
    (fun _ => c) p ∂N) =
    ⨆ n, (∫⁻ p, (Ioc s t ×ˢ B n).indicator (fun _ => c) p ∂N)
  calc
    _ = c * N (Ioc s t ×ˢ (⋃ n, B n)) :=
      lintegral_indicator_const (measurableSet_Ioc.prod hUnion) c
    _ = c * (⨆ n, N (Ioc s t ×ˢ B n)) := by rw [hCount]
    _ = ⨆ n, c * N (Ioc s t ×ˢ B n) := by rw [ENNReal.mul_iSup]
    _ = _ := by
      apply iSup_congr
      intro n
      exact (lintegral_indicator_const
        (measurableSet_Ioc.prod (hB n)) c).symm
