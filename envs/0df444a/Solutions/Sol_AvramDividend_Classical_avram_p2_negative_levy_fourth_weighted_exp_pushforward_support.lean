-- Prove2me | solution 1 for AvramDividend.Classical.avram_p2_negative_levy_fourth_weighted_exp_pushforward_support
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T08:29:11.885555+00:00
-- url     : https://prove2.me/submissions/ab9852e5-dd06-4b85-8577-71899eb0e747

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p2_negative_levy_fourth_weighted_exp_pushforward_finite

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal

/-- The finite weighted Levy image is carried by strictly
positive exponential marks below one, with no mass at or above one. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ} (X : SpectrallyNegativeLevy P 𝓕) :
    (((X.ν.restrict (Iio (0 : ℝ))).withDensity
      (fun y => ENNReal.ofReal ((Real.exp y - 1) ^ 4))).map
      Real.exp) (Ici (1 : ℝ)) = 0 := by
  have hdisj : Disjoint
      (Real.exp ⁻¹' Ici (1 : ℝ)) (Iio (0 : ℝ)) := by
    rw [Set.disjoint_left]
    intro y hy1 hy2
    exact (not_le.mpr (Real.exp_lt_one_iff.mpr hy2)) hy1
  have hm : MeasurableSet (Real.exp ⁻¹' Ici (1 : ℝ)) :=
    measurableSet_Ici.preimage Real.measurable_exp
  have hzero :
      (X.ν.restrict (Iio (0 : ℝ)))
        (Real.exp ⁻¹' Ici (1 : ℝ)) = 0 := by
    rw [Measure.restrict_apply hm]
    rw [Set.disjoint_iff_inter_eq_empty.mp hdisj]
    exact measure_empty
  have hac := withDensity_absolutelyContinuous
    (X.ν.restrict (Iio (0 : ℝ)))
      (fun y => ENNReal.ofReal ((Real.exp y - 1) ^ 4))
  have hzero' :
      ((X.ν.restrict (Iio (0 : ℝ))).withDensity
        (fun y => ENNReal.ofReal ((Real.exp y - 1) ^ 4)))
        (Real.exp ⁻¹' Ici (1 : ℝ)) = 0 :=
    hac hzero
  exact (Measure.map_apply Real.measurable_exp measurableSet_Ici).trans hzero'
