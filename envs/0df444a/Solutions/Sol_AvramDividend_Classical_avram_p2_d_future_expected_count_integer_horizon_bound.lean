-- Prove2me | solution 1 for AvramDividend.Classical.avram_p2_d_future_expected_count_integer_horizon_bound
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T19:01:28.031288+00:00
-- url     : https://prove2.me/submissions/a917371d-cfdb-4f29-858c-262fb43315c9

import Mathlib.MeasureTheory.Measure.Count
import Mathlib.Topology.Order.LeftRightLim
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p2_d_future_zero_origin_expected_count_monotone
import Theorems.Thm_AvramDividend_Classical_avram_p2_d_future_zero_origin_expected_count_nat_scaling

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal

/-- The original marked jump-count mean over any bounded horizon is bounded
by the integer ceiling multiple of the original first-unit marked mean. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (B : Set ℝ) (hB : MeasurableSet B)
    (t : ℝ≥0) (n : ℕ) (ht : t ≤ (n : ℝ≥0)) :
    (∫⁻ ω, ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u,
          X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
        (Ioc 0 t ×ˢ B) ∂P) ≤ (n : ℝ≥0∞) * (∫⁻ ω, ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u,
          X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
        (Ioc 0 (1 : ℝ≥0) ×ˢ B) ∂P) := by
  let M : ℝ≥0 → ℝ≥0∞ := fun q => (∫⁻ ω, ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u,
          X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
        (Ioc 0 q ×ˢ B) ∂P)
  have hMon : M t ≤ M (n : ℝ≥0) := by
    simpa only [M] using
      (avram_p2_d_future_zero_origin_expected_count_monotone
        X t (n : ℝ≥0) ht B)
  have hNat : M (n : ℝ≥0) = (n : ℝ≥0∞) * M 1 := by
    simpa only [M] using
      (avram_p2_d_future_zero_origin_expected_count_nat_scaling X B hB n)
  change M t ≤ (n : ℝ≥0∞) * M 1
  calc
    M t ≤ M (n : ℝ≥0) := hMon
    _ = (n : ℝ≥0∞) * M 1 := hNat
