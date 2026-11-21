-- Prove2me | solution 1 for AvramDividend.Classical.avram_mix_inf20_original_above_finitecap_full_generator_reduces_to_drift_jump
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-20T12:43:30.168184+00:00
-- url     : https://prove2.me/submissions/b27a0110-d370-43b2-b859-0a97689524bb

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_gbB31_interior_caplinear_affine_upper_derivatives
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section
set_option autoImplicit false

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (w : ℝ → ℝ) (b y : ℝ) (hy : b < y) :
    let V : ℝ → ℝ := fun t =>
      if t ≤ b then w t else w b + (t - b)
    X.generator V y = X.c +
      (∫ z in Iio (0 : ℝ),
        SpectrallyNegativeLevy.generatorIntegrand V y z ∂X.ν) := by
  dsimp only
  obtain ⟨hd, h2⟩ :=
    avram_gbB31_interior_caplinear_affine_upper_derivatives w b y hy
  simp [SpectrallyNegativeLevy.generator, hd, h2]
