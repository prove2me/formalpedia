-- Prove2me | solution 1 for AvramDividend.Classical.avram_a89_original_fullnegative_future_void_stationary_exact_20261114
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-14T18:20:37.213285+00:00
-- url     : https://prove2.me/submissions/da171cab-377d-49e8-9608-9f80540b6966

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p4_s3_interval_h_original_intrinsic_marked_count_stationary_law
import Theorems.Thm_AvramDividend_Classical_avram_p2_e_compensator_intrinsic_rectangle_count_measurable
import Theorems.Thm_AvramDividend_Classical_avram_a82_original_finiteactivity_fullnegative_nojump_probability_20261114
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
    (s T : ℝ≥0) :
    P {ω : Ω |
      ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u,
          X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
        (Ioc s (s + T) ×ˢ Iio (0 : ℝ)) = 0} =
      ENNReal.ofReal (Real.exp
        (-((T : ℝ) * (X.ν (Iio (0 : ℝ))).toReal))) := by
  let NX : Ω → Measure (ℝ≥0 × ℝ) := fun ω =>
    ((Measure.count.restrict {u : ℝ≥0 |
      0 < u ∧ X.X u ω -
        Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
      (fun u : ℝ≥0 => (u,
        X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
  let FS : Ω → ℝ≥0∞ := fun ω => NX ω (Ioc s (s + T) ×ˢ Iio (0 : ℝ))
  let F0 : Ω → ℝ≥0∞ := fun ω => NX ω (Ioc 0 T ×ˢ Iio (0 : ℝ))
  have hsT : s ≤ s + T := le_add_of_nonneg_right (by positivity : 0 ≤ T)
  have hmS : Measurable FS := by
    exact avram_p2_e_compensator_intrinsic_rectangle_count_measurable
      X s (s + T) hsT (Iio (0 : ℝ)) measurableSet_Iio
  have hm0 : Measurable F0 := by
    exact avram_p2_e_compensator_intrinsic_rectangle_count_measurable
      X 0 T (by positivity : 0 ≤ T) (Iio (0 : ℝ)) measurableSet_Iio
  have hLaw : Measure.map FS P = Measure.map F0 P := by
    exact avram_p4_s3_interval_h_original_intrinsic_marked_count_stationary_law
      X NX (by intro ω; rfl) s T (Iio (0 : ℝ)) measurableSet_Iio
  have hVoid := congrArg (fun μ : Measure ℝ≥0∞ => μ {0}) hLaw
  rw [Measure.map_apply hmS (measurableSet_singleton (0 : ℝ≥0∞)),
      Measure.map_apply hm0 (measurableSet_singleton (0 : ℝ≥0∞))] at hVoid
  change P {ω | FS ω = 0} = P {ω | F0 ω = 0} at hVoid
  exact hVoid.trans
    (avram_a82_original_finiteactivity_fullnegative_nojump_probability_20261114
      X hFinite T)
