-- Prove2me | solution 1 for AvramDividend.Classical.avram_p2_34dbea70_original_marked_mean_iUnion_increasing_marks
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T15:21:14.601167+00:00
-- url     : https://prove2.me/submissions/8d21e73e-37ef-4f01-b6c6-e3e8e9a74020

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p2_a_zero_rate_intrinsic_band_count_measurable
import Theorems.Thm_AvramDividend_Classical_avram_p2_34dbea70_increasing_borel_mark_rectangle_measure_iUnion

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal

/-- Continuity from below of the original intrinsic jump-count expectation. -/
theorem solution {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (T : ℝ≥0)
    (B : ℕ → Set ℝ) (hB : ∀ n, MeasurableSet (B n))
    (hmono : Monotone B) :
    (∫⁻ ω, ((Measure.count.restrict {u : ℝ≥0 | 0 < u ∧
      X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
      (fun u : ℝ≥0 =>
        (u, X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
      (Ioc 0 T ×ˢ (⋃ n, B n)) ∂P) =
    ⨆ n, (∫⁻ ω, ((Measure.count.restrict {u : ℝ≥0 | 0 < u ∧
      X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
      (fun u : ℝ≥0 =>
        (u, X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
      (Ioc 0 T ×ˢ B n) ∂P) := by
  let N : Ω → Measure (ℝ≥0 × ℝ) := fun ω =>
    ((Measure.count.restrict {u : ℝ≥0 | 0 < u ∧
      X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
      (fun u : ℝ≥0 =>
        (u, X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
  change (∫⁻ ω, N ω (Ioc 0 T ×ˢ (⋃ n, B n)) ∂P) =
    ⨆ n, (∫⁻ ω, N ω (Ioc 0 T ×ˢ B n) ∂P)
  have hmono_count : Monotone
      (fun n : ℕ => fun ω : Ω => N ω (Ioc 0 T ×ˢ B n)) := by
    intro m n hmn ω
    apply MeasureTheory.measure_mono
    exact Set.prod_mono (Subset.rfl) (hmono hmn)
  have hmeas_count (n : ℕ) :
      Measurable (fun ω : Ω => N ω (Ioc 0 T ×ˢ B n)) :=
    avram_p2_a_zero_rate_intrinsic_band_count_measurable X T (B n) (hB n)
  calc
    _ = (∫⁻ ω, ⨆ n, N ω (Ioc 0 T ×ˢ B n) ∂P) := by
      congr 1
      funext ω
      exact avram_p2_34dbea70_increasing_borel_mark_rectangle_measure_iUnion
        (N ω) T B hmono
    _ = _ := by
      exact lintegral_iSup hmeas_count hmono_count
