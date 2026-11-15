-- Prove2me | solution 1 for AvramDividend.Classical.avram_a90_original_fullnegative_future_void_conditional_factor_20261114
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-14T18:31:11.147139+00:00
-- url     : https://prove2.me/submissions/d27102ba-230e-44b8-bccd-55ceb44399a9

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave7_06_original_intrinsic_future_mark_void_event_probability_factor
import Theorems.Thm_AvramDividend_Classical_avram_a89_original_fullnegative_future_void_stationary_exact_20261114
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hFinite : X.ν (Iio (0 : ℝ)) ≠ ⊤)
    (s T : ℝ≥0)
    (A : Set Ω) (hPast : MeasurableSet[𝓕 s] A)
    (hRaw : MeasurableSet A) :
    P (A ∩ {ω : Ω |
      ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u,
          X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
        (Ioc s (s + T) ×ˢ Iio (0 : ℝ)) = 0}) =
      P A * ENNReal.ofReal (Real.exp
        (-((T : ℝ) * (X.ν (Iio (0 : ℝ))).toReal))) := by
  have hIndep :=
    avram_wave7_06_original_intrinsic_future_mark_void_event_probability_factor
      X s (s + T) (le_add_of_nonneg_right (by positivity : 0 ≤ T))
      (Iio (0 : ℝ)) measurableSet_Iio A hPast hRaw
  have hExact :=
    avram_a89_original_fullnegative_future_void_stationary_exact_20261114
      X hFinite s T
  rw [hExact] at hIndep
  exact hIndep
