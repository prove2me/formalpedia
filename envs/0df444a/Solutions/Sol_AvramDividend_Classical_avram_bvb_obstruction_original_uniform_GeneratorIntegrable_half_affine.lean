-- Prove2me | solution 1 for AvramDividend.Classical.avram_bvb_obstruction_original_uniform_GeneratorIntegrable_half_affine
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-15T07:37:51.12253+00:00
-- url     : https://prove2.me/submissions/771eac3a-a6c4-4599-a376-cacd2bedd97b

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_bvb_obstruction_uniform_crossing_kernel_integrableOn
import Theorems.Thm_AvramDividend_Classical_avram_bvb_obstruction_uniform_affine_generator_integrand_crossing_exact
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
    X.GeneratorIntegrable w y := by
  change Integrable (SpectrallyNegativeLevy.generatorIntegrand w y)
    (X.ν.restrict (Iio (0 : ℝ)))
  have hset : Iio (0 : ℝ) ∩ Ioo (-1 : ℝ) 0 =
      Ioo (-1 : ℝ) 0 := by
    ext z
    simp only [Set.mem_inter_iff, Set.mem_Iio, Set.mem_Ioo]
    tauto
  rw [hν, Measure.restrict_restrict measurableSet_Iio, hset]
  change IntegrableOn (SpectrallyNegativeLevy.generatorIntegrand w y)
    (Ioo (-1 : ℝ) 0) (volume : Measure ℝ)
  have hEq : EqOn (SpectrallyNegativeLevy.generatorIntegrand w y)
      (fun z : ℝ => if y + z < 0 then -(y + (1 / 2 : ℝ) + z) else 0)
      (Ioo (-1 : ℝ) 0) := by
    intro z hz
    exact avram_bvb_obstruction_uniform_affine_generator_integrand_crossing_exact
      y z hy hz w hw hd
  exact (integrableOn_congr_fun hEq measurableSet_Ioo).2
    (avram_bvb_obstruction_uniform_crossing_kernel_integrableOn y)
