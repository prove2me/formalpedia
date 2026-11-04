-- Prove2me | solution 1 for AvramDividend.Classical.avram_p2_original_fourth_weighted_exp_pushforward_nonpositive_null
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T08:45:02.235682+00:00
-- url     : https://prove2.me/submissions/f16b56dd-1ef0-47a0-ba0d-fd1f6ff20edd

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p2_original_tilted_weighted_exponential_pushforward_finite

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal

/-- The genuine original fourth-weighted exponential image is carried
by strictly positive marks for every observation time. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ} (X : SpectrallyNegativeLevy P 𝓕)
    (t : ℝ≥0) :
    ((P.withDensity (fun ω => ENNReal.ofReal
      ((Real.exp (X.X t ω) - 1) ^ 4))).map
      (fun ω => Real.exp (X.X t ω))) (Iic (0 : ℝ)) = 0 := by
  have hXm : Measurable (X.X t) :=
    (X.adapted t).mono (𝓕.le t) le_rfl
  have hG : Measurable (fun ω : Ω => Real.exp (X.X t ω)) :=
    Real.measurable_exp.comp hXm
  have hpre : (fun ω : Ω => Real.exp (X.X t ω)) ⁻¹'
      Iic (0 : ℝ) = ∅ := by
    ext ω
    simp only [Set.mem_preimage, Set.mem_Iic, Set.mem_empty_iff_false,
      iff_false]
    exact not_le.mpr (Real.exp_pos _)
  rw [Measure.map_apply hG measurableSet_Iic, hpre]
  exact measure_empty
