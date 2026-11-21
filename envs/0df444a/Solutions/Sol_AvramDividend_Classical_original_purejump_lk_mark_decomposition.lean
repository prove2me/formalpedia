-- Prove2me | solution 1 for AvramDividend.Classical.original_purejump_lk_mark_decomposition
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-20T22:36:42.69523+00:00
-- url     : https://prove2.me/submissions/14556f88-7606-4031-9362-5ed9390ad973
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_ja18g_original_large_negative_signed_mark_integrable
import Theorems.Thm_AvramDividend_Classical_original_negative_mark_integral_compensation
set_option autoImplicit false
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hσ : X.σ = 0) (θ : ℝ) (hθ : 0 < θ)
    (hFn : Integrable
      (fun y : ℝ => ∫ t in (0 : ℝ)..(-y), 1 - Real.exp (-θ * t)) X.ν) :
    X.ψ θ / θ =
      X.c + (∫ y in Iic (-1 : ℝ), y ∂X.ν) +
      (∫ y : ℝ, ∫ t in (0 : ℝ)..(-y),
        1 - Real.exp (-θ * t) ∂X.ν) := by
  have hInt := original_negative_mark_integral_compensation
    X.ν X.ν_Ici θ hθ
    (avram_ja18g_original_large_negative_signed_mark_integrable X hX) hFn
  have hν : X.ν.restrict (Iio (0 : ℝ)) = X.ν := by
    apply Measure.restrict_eq_self_of_ae_mem
    filter_upwards [measure_eq_zero_iff_ae_notMem.mp X.ν_Ici] with y hy
    exact lt_of_not_ge (by simpa only [mem_Ici] using hy)
  have hPsi : X.ψ θ =
      X.c * θ + ∫ y : ℝ,
        Real.exp (θ * y) - 1 -
          θ * y * (Ioo (-1 : ℝ) 1).indicator 1 y ∂X.ν := by
    simp [SpectrallyNegativeLevy.ψ, laplaceExponent, hσ, hν]
  rw [hPsi, hInt]
  have hθ0 : θ ≠ 0 := ne_of_gt hθ
  field_simp [hθ0]
  ring
