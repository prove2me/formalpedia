-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave7_01_original_nonnegative_mark_arbitrary_reward_integral_zero
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-02T15:02:07.2117+00:00
-- url     : https://prove2.me/submissions/24107193-76cb-4f9c-9abe-72559e670056

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave5_01_actual_intrinsic_marked_measure_global_nonnegative_support_zero

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (ω : Ω)
    (K : (ℝ≥0 × ℝ) → ℝ≥0∞) :
    (∫⁻ p in (Set.univ ×ˢ Ici (0 : ℝ)), K p ∂
      ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u,
          X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))) = 0 := by
  let μ : Measure (ℝ≥0 × ℝ) :=
    (Measure.count.restrict {u : ℝ≥0 |
      0 < u ∧ X.X u ω -
        Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
      (fun u : ℝ≥0 => (u,
        X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u))
  have hZero : μ (Set.univ ×ˢ Ici (0 : ℝ)) = 0 :=
    avram_wave5_01_actual_intrinsic_marked_measure_global_nonnegative_support_zero X ω
  have hRestrict : μ.restrict (Set.univ ×ˢ Ici (0 : ℝ)) = 0 :=
    Measure.restrict_eq_zero.mpr hZero
  change (∫⁻ p, K p ∂(μ.restrict (Set.univ ×ˢ Ici (0 : ℝ)))) = 0
  rw [hRestrict]
  exact lintegral_zero_measure K
