-- Prove2me | solution 1 for AvramDividend.Classical.avram_bvb_obstruction_original_uniform_mark_generator_integral_exact
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-15T01:11:47.922931+00:00
-- url     : https://prove2.me/submissions/c4727b09-0166-46ed-a66c-23c75d30ef7a
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_AvramDividend_Classical_avram_bvb_obstruction_uniform_affine_generator_integrand_crossing_exact
import Theorems.Thm_AvramDividend_Classical_avram_bvb_obstruction_uniform_half_affine_compensated_kernel_integral_exact
import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hν : X.ν = (volume : Measure ℝ).restrict (Ioo (-1 : ℝ) 0))
    (y : ℝ) (hy : 0 < y) (w : ℝ → ℝ)
    (hw : ∀ u : ℝ, w u = if u < 0 then 0 else 1 / 2 + u)
    (hd : deriv w y = 1) :
    (∫ z in Iio (0 : ℝ),
       SpectrallyNegativeLevy.generatorIntegrand w y z ∂X.ν) =
      if y < 1 then y * (y - 1) / 2 else 0 := by
  have hSet : Iio (0 : ℝ) ∩ Ioo (-1 : ℝ) 0 =
      Ioo (-1 : ℝ) 0 := by
    ext z
    simp only [Set.mem_inter_iff, Set.mem_Iio, Set.mem_Ioo]
    constructor
    · intro h
      exact h.2
    · intro h
      exact ⟨h.2, h⟩
  have hRestrict :
      (X.ν.restrict (Iio (0 : ℝ))) =
      ((volume : Measure ℝ).restrict (Ioo (-1 : ℝ) 0)) := by
    rw [hν, Measure.restrict_restrict measurableSet_Iio, hSet]
  change (∫ z,
      SpectrallyNegativeLevy.generatorIntegrand w y z
        ∂(X.ν.restrict (Iio (0 : ℝ)))) = _
  rw [hRestrict]
  change (∫ z in Ioo (-1 : ℝ) 0,
      SpectrallyNegativeLevy.generatorIntegrand w y z
        ∂(volume : Measure ℝ)) = _
  calc
    _ = ∫ z in Ioo (-1 : ℝ) 0,
        (if y + z < 0 then -(y + (1 / 2 : ℝ) + z) else 0)
          ∂(volume : Measure ℝ) := by
          apply setIntegral_congr_fun measurableSet_Ioo
          intro z hz
          exact AvramDividend.Classical.avram_bvb_obstruction_uniform_affine_generator_integrand_crossing_exact
            y z hy hz w hw hd
    _ = _ :=
      AvramDividend.Classical.avram_bvb_obstruction_uniform_half_affine_compensated_kernel_integral_exact
        y hy
