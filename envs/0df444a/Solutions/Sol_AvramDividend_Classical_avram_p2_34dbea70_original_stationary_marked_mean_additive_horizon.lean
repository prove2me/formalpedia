-- Prove2me | solution 1 for AvramDividend.Classical.avram_p2_34dbea70_original_stationary_marked_mean_additive_horizon
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T13:46:39.053476+00:00
-- url     : https://prove2.me/submissions/de58879c-0a73-49fc-996b-03834c9ea692

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave7_01_original_intrinsic_marked_rectangle_count_stationary_mean
import Theorems.Thm_AvramDividend_Classical_avram_p2_34dbea70_marked_rectangle_time_concatenation

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal

/-- Stationarity and pathwise rectangle splitting give additive count means. -/
theorem solution {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (T S : ℝ≥0)
    (B : Set ℝ) (hB : MeasurableSet B)
    (hCountMeas : Measurable (fun ω =>
      ((Measure.count.restrict {u : ℝ≥0 | 0 < u ∧
        X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 =>
          (u, X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
        (Ioc 0 T ×ˢ B))) :
    (∫⁻ ω, ((Measure.count.restrict {u : ℝ≥0 | 0 < u ∧
      X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
      (fun u : ℝ≥0 =>
        (u, X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
      (Ioc 0 (T + S) ×ˢ B) ∂P) =
    (∫⁻ ω, ((Measure.count.restrict {u : ℝ≥0 | 0 < u ∧
      X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
      (fun u : ℝ≥0 =>
        (u, X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
      (Ioc 0 T ×ˢ B) ∂P) +
    (∫⁻ ω, ((Measure.count.restrict {u : ℝ≥0 | 0 < u ∧
      X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
      (fun u : ℝ≥0 =>
        (u, X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
      (Ioc 0 S ×ˢ B) ∂P) := by
  let N : Ω → Measure (ℝ≥0 × ℝ) := fun ω =>
    ((Measure.count.restrict {u : ℝ≥0 | 0 < u ∧
      X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
      (fun u : ℝ≥0 =>
        (u, X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
  change (∫⁻ ω, N ω (Ioc 0 (T + S) ×ˢ B) ∂P) =
    (∫⁻ ω, N ω (Ioc 0 T ×ˢ B) ∂P) +
      (∫⁻ ω, N ω (Ioc 0 S ×ˢ B) ∂P)
  calc
    _ = (∫⁻ ω, N ω (Ioc 0 T ×ˢ B) +
      N ω (Ioc T (T + S) ×ˢ B) ∂P) := by
        congr 1
        funext ω
        exact avram_p2_34dbea70_marked_rectangle_time_concatenation
          (N ω) T S B hB
    _ = (∫⁻ ω, N ω (Ioc 0 T ×ˢ B) ∂P) +
      (∫⁻ ω, N ω (Ioc T (T + S) ×ˢ B) ∂P) := by
        exact lintegral_add_left hCountMeas _
    _ = _ := by
      rw [avram_wave7_01_original_intrinsic_marked_rectangle_count_stationary_mean
        X T S B hB]
