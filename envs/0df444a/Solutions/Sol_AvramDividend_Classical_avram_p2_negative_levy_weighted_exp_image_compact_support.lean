-- Prove2me | solution 1 for AvramDividend.Classical.avram_p2_negative_levy_weighted_exp_image_compact_support
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T08:51:39.879204+00:00
-- url     : https://prove2.me/submissions/907f6081-b44b-4447-b6c2-df9bcddc00fe

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p2_negative_levy_fourth_weighted_exp_pushforward_support

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal

/-- The finite fourth-weighted exponential image of the actual negative
Levy measure is supported on the compact interval [0,1]. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ} (X : SpectrallyNegativeLevy P 𝓕) :
    (((X.ν.restrict (Iio (0 : ℝ))).withDensity
      (fun y => ENNReal.ofReal ((Real.exp y - 1) ^ 4))).map
      Real.exp) ((Icc (0 : ℝ) 1)ᶜ) = 0 := by
  let μ : Measure ℝ :=
    (((X.ν.restrict (Iio (0 : ℝ))).withDensity
      (fun y => ENNReal.ofReal ((Real.exp y - 1) ^ 4))).map Real.exp)
  change μ ((Icc (0 : ℝ) 1)ᶜ) = 0
  have hright : μ (Ici (1 : ℝ)) = 0 :=
    avram_p2_negative_levy_fourth_weighted_exp_pushforward_support X
  have hpre : Real.exp ⁻¹' Iic (0 : ℝ) = ∅ := by
    ext y
    simp only [Set.mem_preimage, Set.mem_Iic, Set.mem_empty_iff_false,
      iff_false]
    exact not_le.mpr (Real.exp_pos y)
  have hleft : μ (Iic (0 : ℝ)) = 0 := by
    change (((X.ν.restrict (Iio (0 : ℝ))).withDensity
      (fun y => ENNReal.ofReal ((Real.exp y - 1) ^ 4))).map
      Real.exp) (Iic (0 : ℝ)) = 0
    rw [Measure.map_apply Real.measurable_exp measurableSet_Iic, hpre]
    exact measure_empty
  have hsubset : (Icc (0 : ℝ) 1)ᶜ ⊆ Iic 0 ∪ Ici 1 := by
    intro z hz
    by_cases hz0 : z ≤ 0
    · exact Or.inl hz0
    · have hzpos : 0 < z := lt_of_not_ge hz0
      have hz1 : 1 ≤ z := by
        by_contra hn
        have hzlt : z < 1 := lt_of_not_ge hn
        exact hz ⟨le_of_lt hzpos, le_of_lt hzlt⟩
      exact Or.inr hz1
  apply le_antisymm ?_ zero_le
  calc
    μ ((Icc (0 : ℝ) 1)ᶜ) ≤ μ (Iic 0 ∪ Ici 1) :=
      measure_mono hsubset
    _ ≤ μ (Iic 0) + μ (Ici 1) := measure_union_le _ _
    _ = 0 := by rw [hleft, hright]; simp
