-- Prove2me | solution 1 for AvramDividend.Classical.avram_p2_34dbea70_original_disjoint_borel_mark_mean_add
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T15:01:56.292184+00:00
-- url     : https://prove2.me/submissions/46b2ad7f-335b-44fd-9904-b8992f4b1f2b

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p2_a_zero_rate_intrinsic_band_count_measurable
import Theorems.Thm_AvramDividend_Classical_avram_p2_34dbea70_marked_rectangle_disjoint_mark_add

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal

/-- Expected intrinsic marks of the unchanged original source are finitely additive. -/
theorem solution {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (T : ℝ≥0)
    (B C : Set ℝ) (hB : MeasurableSet B) (hC : MeasurableSet C)
    (hBC : Disjoint B C) :
    (∫⁻ ω, ((Measure.count.restrict {u : ℝ≥0 | 0 < u ∧
      X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
      (fun u : ℝ≥0 =>
        (u, X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
      (Ioc 0 T ×ˢ (B ∪ C)) ∂P) =
    (∫⁻ ω, ((Measure.count.restrict {u : ℝ≥0 | 0 < u ∧
      X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
      (fun u : ℝ≥0 =>
        (u, X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
      (Ioc 0 T ×ˢ B) ∂P) +
    (∫⁻ ω, ((Measure.count.restrict {u : ℝ≥0 | 0 < u ∧
      X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
      (fun u : ℝ≥0 =>
        (u, X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
      (Ioc 0 T ×ˢ C) ∂P) := by
  let N : Ω → Measure (ℝ≥0 × ℝ) := fun ω =>
    ((Measure.count.restrict {u : ℝ≥0 | 0 < u ∧
      X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
      (fun u : ℝ≥0 =>
        (u, X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
  change (∫⁻ ω, N ω (Ioc 0 T ×ˢ (B ∪ C)) ∂P) =
    (∫⁻ ω, N ω (Ioc 0 T ×ˢ B) ∂P) +
      (∫⁻ ω, N ω (Ioc 0 T ×ˢ C) ∂P)
  calc
    _ = (∫⁻ ω, N ω (Ioc 0 T ×ˢ B) + N ω (Ioc 0 T ×ˢ C) ∂P) := by
      congr 1
      funext ω
      exact avram_p2_34dbea70_marked_rectangle_disjoint_mark_add
        (N ω) T B C hB hC hBC
    _ = _ := by
      exact lintegral_add_left
        (avram_p2_a_zero_rate_intrinsic_band_count_measurable X T B hB) _
