-- Prove2me | solution 1 for AvramDividend.Classical.avram_p2_d_future_original_zero_origin_all_real_source_rate
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T20:39:40.274449+00:00
-- url     : https://prove2.me/submissions/86ad2fcb-599e-4c04-ad03-96a2b9e65a75

import Mathlib.MeasureTheory.Measure.Count
import Mathlib.Topology.Order.LeftRightLim
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p2_d_future_original_finite_unit_mean_exact_real_horizon_rate
import Theorems.Thm_AvramDividend_Classical_avram_p2_d_future_unit_mean_infinite_positive_real_horizon
import Theorems.Thm_AvramDividend_Classical_avram_p2_d_future_original_empty_time_window_mean_zero

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal

/-- Exact original marked-count time-rate linearity, including zero time
and infinite source unit-time intensity, without identifying it with X.ν. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (B : Set ℝ) (hB : MeasurableSet B)
    (t : ℝ≥0) :
    (∫⁻ ω, ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u,
          X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
        (Ioc 0 t ×ˢ B) ∂P) = (t : ℝ≥0∞) * (∫⁻ ω, ((Measure.count.restrict {u : ℝ≥0 |
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
  change M t = (t : ℝ≥0∞) * M 1
  by_cases hfin : M 1 < ⊤
  · exact avram_p2_d_future_original_finite_unit_mean_exact_real_horizon_rate
      X B hB t hfin
  · have htop : M 1 = ⊤ := top_unique (le_of_not_gt hfin)
    by_cases hz : t = 0
    · subst t
      have he : M 0 = 0 :=
        avram_p2_d_future_original_empty_time_window_mean_zero X 0 B
      simpa using he
    · have hp : 0 < t := pos_iff_ne_zero.mpr hz
      have ht : M t = ⊤ :=
        avram_p2_d_future_unit_mean_infinite_positive_real_horizon
          X B hB t hp htop
      have htnonzero : (t : ℝ≥0∞) ≠ 0 := by
        exact_mod_cast (ne_of_gt hp)
      calc
        M t = ⊤ := ht
        _ = (t : ℝ≥0∞) * M 1 := by simp [htop, htnonzero]
