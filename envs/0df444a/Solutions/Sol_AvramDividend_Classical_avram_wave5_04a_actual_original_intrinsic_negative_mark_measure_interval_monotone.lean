-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave5_04a_actual_original_intrinsic_negative_mark_measure_interval_monotone
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-01T17:30:05.656965+00:00
-- url     : https://prove2.me/submissions/50af9243-6201-4af1-b71e-4c68cdfc390f

import Mathlib.Topology.Algebra.InfiniteSum.ENNReal
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave5_04a_actual_original_intrinsic_negative_mark_interval_integral_eq_left_jump_sum
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Mathlib.Topology.Order.LeftRightLim

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter Set Topology AvramDividend.Classical
open scoped NNReal ENNReal BigOperators

/-- The genuine original source intrinsic negative-mark mass of a
smaller time window is dominated by its mass on an extended window,
pathwise even in the presence of infinite jump activity. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (ω : Ω)
    (s t r : ℝ≥0) (hst : s ≤ t) (htr : t ≤ r) :
    (∫⁻ p,
      (if s < p.1 ∧ p.1 ≤ t then ENNReal.ofReal (-p.2) else 0) ∂
      ((Measure.count.restrict {u : ℝ≥0 | 0 < u ∧
        X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u,
          X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))) ≤
    (∫⁻ p,
      (if s < p.1 ∧ p.1 ≤ r then ENNReal.ofReal (-p.2) else 0) ∂
      ((Measure.count.restrict {u : ℝ≥0 | 0 < u ∧
        X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u,
          X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))) := by
  rw [avram_wave5_04a_actual_original_intrinsic_negative_mark_interval_integral_eq_left_jump_sum
      X ω s t,
    avram_wave5_04a_actual_original_intrinsic_negative_mark_interval_integral_eq_left_jump_sum
      X ω s r]
  apply ENNReal.tsum_le_tsum
  intro u
  by_cases hs : s < u
  · by_cases ht : u ≤ t
    · have hr : u ≤ r := ht.trans htr
      simp [hs, ht, hr]
    · simp [hs, ht]
  · simp [hs]
