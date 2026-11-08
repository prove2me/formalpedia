-- Prove2me | solution 1 for AvramDividend.Classical.avram_a19_affine_singular_large_reserve_integrand_zero
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-07T16:46:11.420468+00:00
-- url     : https://prove2.me/submissions/7054f252-a060-42a3-a9f9-e30cff0d9303

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_a19_affine_zero_extension_deriv_one

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Classical MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- A sufficiently large positive reserve gives zero compensated integrand at a small negative jump. -/
theorem solution
    (x z : ℝ) (hx : 1 ≤ x) (hz : z ∈ Ioo (-1 : ℝ) 0) :
    SpectrallyNegativeLevy.generatorIntegrand
      (fun u : ℝ => if u < 0 then (0 : ℝ) else 1 + u) x z = 0 := by
  have hxpos : 0 < x := by linarith
  have hpos : 0 < x + z := by linarith [hz.1]
  have hzsmall : z ∈ Ioo (-1 : ℝ) 1 := ⟨hz.1, by linarith [hz.2]⟩
  have hderiv := avram_a19_affine_zero_extension_deriv_one x hxpos
  simp [SpectrallyNegativeLevy.generatorIntegrand,
    not_lt.mpr (le_of_lt hxpos), not_lt.mpr (le_of_lt hpos), hzsmall, hderiv] <;> ring
