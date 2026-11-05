-- Prove2me | solution 1 for AvramDividend.Classical.avram_p4_b_smalljump_original_quadratic_weighted_levy_measure_zero_atom
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-04T07:56:28.950364+00:00
-- url     : https://prove2.me/submissions/5ba26943-e13b-43b5-b4c6-d377ef619f73

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal

/-- The actual source Lévy measure weighted by squared jump size has
zero mass at the origin, regardless of the unweighted atom convention. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) :
    (X.ν.withDensity (fun z : ℝ => ENNReal.ofReal (z ^ 2)))
      ({0} : Set ℝ) = 0 := by
  have hMeas : Measurable (fun z : ℝ => ENNReal.ofReal (z ^ 2)) :=
    ENNReal.measurable_ofReal.comp (measurable_id.pow_const 2)
  rw [withDensity_apply_eq_zero hMeas]
  have hEmpty : {z : ℝ | ENNReal.ofReal (z ^ 2) ≠ 0} ∩
      ({0} : Set ℝ) = ∅ := by
    ext z
    simp
  rw [hEmpty]
  exact measure_empty
