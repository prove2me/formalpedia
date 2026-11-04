-- Prove2me | solution 1 for AvramDividend.Classical.avram_p2_34dbea70_original_marked_mean_countable_disjoint_add
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T15:41:32.967198+00:00
-- url     : https://prove2.me/submissions/23bc7c46-26aa-497e-959e-5b940f71a50b

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p2_a_zero_rate_intrinsic_band_count_measurable
import Theorems.Thm_AvramDividend_Classical_avram_p2_34dbea70_disjoint_marked_rectangle_countable_add

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal BigOperators

/-- The unchanged original jump-count expectation is countably additive in disjoint marks. -/
theorem solution {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (T : ℝ≥0)
    (B : ℕ → Set ℝ) (hB : ∀ n, MeasurableSet (B n))
    (hDisj : Pairwise (Function.onFun Disjoint B)) :
    (∫⁻ ω, ((Measure.count.restrict {u : ℝ≥0 | 0 < u ∧
      X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
      (fun u : ℝ≥0 =>
        (u, X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
      (Ioc 0 T ×ˢ (⋃ n, B n)) ∂P) =
    ∑' n, (∫⁻ ω, ((Measure.count.restrict {u : ℝ≥0 | 0 < u ∧
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
    ∑' n, (∫⁻ ω, N ω (Ioc 0 T ×ˢ B n) ∂P)
  have hmeas (n : ℕ) :
      AEMeasurable (fun ω : Ω => N ω (Ioc 0 T ×ˢ B n)) P :=
    (avram_p2_a_zero_rate_intrinsic_band_count_measurable X T (B n) (hB n)).aemeasurable
  calc
    _ = (∫⁻ ω, ∑' n, N ω (Ioc 0 T ×ˢ B n) ∂P) := by
      congr 1
      funext ω
      exact avram_p2_34dbea70_disjoint_marked_rectangle_countable_add
        (N ω) T B hB hDisj
    _ = _ := lintegral_tsum hmeas
