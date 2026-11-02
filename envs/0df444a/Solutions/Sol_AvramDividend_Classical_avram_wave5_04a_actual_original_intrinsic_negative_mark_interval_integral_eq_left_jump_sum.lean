-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave5_04a_actual_original_intrinsic_negative_mark_interval_integral_eq_left_jump_sum
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-01T14:13:32.71096+00:00
-- url     : https://prove2.me/submissions/aea65f58-d5b3-446e-a416-12bb1365202a

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave4_04a_actual_intrinsic_lintegral_eq_jump_sum

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter Set Topology AvramDividend.Classical
open scoped NNReal ENNReal BigOperators

/-- Pathwise identity: the actual source intrinsic negative-mark integral
on an interval is precisely the all-time sum of its genuine negative
left-jump magnitudes. No Poisson representation is introduced. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (ω : Ω)
    (s t : ℝ≥0) :
    (∫⁻ p,
      (if s < p.1 ∧ p.1 ≤ t then ENNReal.ofReal (-p.2) else 0) ∂
      ((Measure.count.restrict {u : ℝ≥0 | 0 < u ∧
        X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u,
          X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))) =
    ∑' (u : ℝ≥0),
      if s < u ∧ u ≤ t then
        ENNReal.ofReal
          (Function.leftLim (fun v : ℝ≥0 => X.X v ω) u - X.X u ω)
      else 0 := by
  have hmeas :
      Measurable (fun p : ℝ≥0 × ℝ =>
        if s < p.1 ∧ p.1 ≤ t then ENNReal.ofReal (-p.2) else 0) := by
    apply Measurable.ite
      ((measurableSet_lt measurable_const measurable_fst).inter
        (measurableSet_le measurable_fst measurable_const))
    · exact ENNReal.measurable_ofReal.comp (measurable_snd.neg)
    · exact measurable_const
  rw [avram_wave4_04a_actual_intrinsic_lintegral_eq_jump_sum X ω
    (fun p : ℝ≥0 × ℝ =>
      if s < p.1 ∧ p.1 ≤ t then ENNReal.ofReal (-p.2) else 0) hmeas]
  apply tsum_congr
  intro u
  by_cases hs : s < u
  · have hpos : 0 < u :=
      lt_of_le_of_lt (show (0 : ℝ≥0) ≤ s from zero_le) hs
    by_cases ht : u ≤ t
    · by_cases hmark :
          X.X u ω - Function.leftLim
            (fun v : ℝ≥0 => X.X v ω) u = 0
      · have hzero : Function.leftLim
            (fun v : ℝ≥0 => X.X v ω) u - X.X u ω = 0 := by
          linarith
        simp [hs, ht, hpos, hmark, hzero]
      · simpa [hs, ht, hpos, hmark, neg_sub]
    · simp [hs, ht]
  · simp [hs]
