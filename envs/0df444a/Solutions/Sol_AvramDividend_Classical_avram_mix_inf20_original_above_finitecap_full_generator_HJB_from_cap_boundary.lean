-- Prove2me | solution 1 for AvramDividend.Classical.avram_mix_inf20_original_above_finitecap_full_generator_HJB_from_cap_boundary
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-20T16:30:41.451095+00:00
-- url     : https://prove2.me/submissions/0c3b645c-f5aa-4cdb-8cf1-8def8e457e4a

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_mix_inf20_original_above_finitecap_full_generator_reduces_to_drift_jump
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section
set_option autoImplicit false

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (w : ℝ → ℝ) (b y q : ℝ)
    (hy : b < y) (hq : 0 ≤ q)
    (hBoundary : X.c +
      (∫ z in Iio (0 : ℝ),
        SpectrallyNegativeLevy.generatorIntegrand
          (fun t => if t ≤ b then w t else w b + (t - b)) b z
        ∂X.ν) - q * w b ≤ 0)
    (hBActual : (∫ z in Iio (0 : ℝ),
        SpectrallyNegativeLevy.generatorIntegrand
          (fun t => if t ≤ b then w t else w b + (t - b)) y z
        ∂X.ν) ≤
        (∫ z in Iio (0 : ℝ),
        SpectrallyNegativeLevy.generatorIntegrand
          (fun t => if t ≤ b then w t else w b + (t - b)) b z
        ∂X.ν)) :
    let V : ℝ → ℝ := fun t =>
      if t ≤ b then w t else w b + (t - b)
    X.generator V y - q * V y ≤ 0 := by
  dsimp only
  rw [avram_mix_inf20_original_above_finitecap_full_generator_reduces_to_drift_jump
    X w b y hy]
  rw [if_neg (not_le.mpr hy)]
  have hqdiff : 0 ≤ q * (y - b) := mul_nonneg hq (le_of_lt (sub_pos.mpr hy))
  linarith
