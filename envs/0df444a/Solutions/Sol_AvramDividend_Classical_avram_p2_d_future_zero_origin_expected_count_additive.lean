-- Prove2me | solution 1 for AvramDividend.Classical.avram_p2_d_future_zero_origin_expected_count_additive
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T17:42:34.023397+00:00
-- url     : https://prove2.me/submissions/be30d897-7f72-4ab3-a81a-e0abe71ccfb3

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p2_d_future_adjacent_window_counts_add
import Theorems.Thm_AvramDividend_Classical_avram_p2_d_future_intrinsic_marked_rectangle_measurable
import Theorems.Thm_AvramDividend_Classical_avram_wave7_01_original_intrinsic_marked_rectangle_count_stationary_mean

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal

/-- The original expected marked count at zero origin is additive in the
physical time horizon; no identification with the Levy measure is used. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (a b : ℝ≥0) (B : Set ℝ) (hB : MeasurableSet B) :
    (∫⁻ ω, ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u,
          X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
        (Ioc 0 (a + b) ×ˢ B) ∂P) =
      (∫⁻ ω, ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u,
          X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
        (Ioc 0 a ×ˢ B) ∂P) +
      (∫⁻ ω, ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u,
          X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
        (Ioc 0 b ×ˢ B) ∂P) := by
  let N (q r : ℝ≥0) (ω : Ω) : ℝ≥0∞ :=
    (Measure.count.restrict {u : ℝ≥0 |
      0 < u ∧ X.X u ω -
        Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
      (fun u : ℝ≥0 => (u,
        X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u))
      (Ioc q r ×ˢ B)
  have hSplit (ω : Ω) :
      N 0 (a + b) ω = N 0 a ω + N a (a + b) ω := by
    simpa only [N] using
      (avram_p2_d_future_adjacent_window_counts_add
        X 0 a (a + b) (show (0 : ℝ≥0) ≤ a from zero_le)
        (le_add_of_nonneg_right (show (0 : ℝ≥0) ≤ b from zero_le)) B hB ω)
  have hMeas : Measurable (N 0 a) := by
    simpa only [N] using
      (avram_p2_d_future_intrinsic_marked_rectangle_measurable X 0 a B hB)
  have hStation :
      (∫⁻ ω, N a (a + b) ω ∂P) =
      (∫⁻ ω, N 0 b ω ∂P) := by
    simpa only [N] using
      (avram_wave7_01_original_intrinsic_marked_rectangle_count_stationary_mean
        X a b B hB)
  change (∫⁻ ω, N 0 (a + b) ω ∂P) =
    (∫⁻ ω, N 0 a ω ∂P) + (∫⁻ ω, N 0 b ω ∂P)
  calc
    (∫⁻ ω, N 0 (a + b) ω ∂P) =
        (∫⁻ ω, N 0 a ω + N a (a + b) ω ∂P) := by
      apply lintegral_congr
      intro ω
      exact hSplit ω
    _ = (∫⁻ ω, N 0 a ω ∂P) +
        (∫⁻ ω, N a (a + b) ω ∂P) :=
      lintegral_add_left hMeas _
    _ = (∫⁻ ω, N 0 a ω ∂P) +
        (∫⁻ ω, N 0 b ω ∂P) := by rw [hStation]
