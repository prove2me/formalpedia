-- Prove2me | solution 1 for AvramDividend.Classical.avram_p4_c_generator_vcstar_interior_cutoff_zero
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T08:16:47.069643+00:00
-- url     : https://prove2.me/submissions/dc2bb3b2-24a0-41e3-9faa-76c49ede726d

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Theorems.Thm_AvramDividend_Classical_generator_vcstar_eq_zero
import Theorems.Thm_AvramDividend_Classical_avram_p4_c_generator_negative_mark_integral_cutoff_split

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing) (q : ℝ) (hq : 0 < q)
    (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (h_smooth : 0 < X.σ ∨ X.BoundedVariation ∨
      ContDiffOn ℝ 2 (vcstar W) (Ioo 0 (cstar W).toReal))
    (hc : 0 < cstar W) (ε : ℝ) (hε : 0 < ε) :
    ∀ y ∈ Ioo 0 (cstar W).toReal,
      X.GeneratorIntegrable (vcstar W) y ∧
      (X.σ ^ 2 / 2 * iteratedDeriv 2 (vcstar W) y +
        X.c * deriv (vcstar W) y +
        (∫ z in Iio (-ε),
          SpectrallyNegativeLevy.generatorIntegrand (vcstar W) y z ∂X.ν) +
        (∫ z in Ico (-ε) 0,
          SpectrallyNegativeLevy.generatorIntegrand (vcstar W) y z ∂X.ν) -
        q * vcstar W y = 0) := by
  intro y hy
  obtain ⟨hI, hEq⟩ := generator_vcstar_eq_zero X hX q hq W hW h_smooth hc y hy
  refine ⟨hI, ?_⟩
  have hsplit :=
    avram_p4_c_generator_negative_mark_integral_cutoff_split X (vcstar W) y ε hε hI
  change X.σ ^ 2 / 2 * iteratedDeriv 2 (vcstar W) y +
      X.c * deriv (vcstar W) y +
      (∫ z in Iio (0 : ℝ),
        SpectrallyNegativeLevy.generatorIntegrand (vcstar W) y z ∂X.ν) -
      q * vcstar W y = 0 at hEq
  rw [hsplit] at hEq
  convert hEq using 1 <;> ring
