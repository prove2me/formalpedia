-- Prove2me | solution 2 for AvramDividend.Classical.original_purejump_laplace_exponent_tail
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-21T07:57:05.583276+00:00
-- url     : https://prove2.me/submissions/1bd68fe9-1a16-4830-8623-5f737fb5865d

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_ja18g_original_large_negative_signed_mark_integrable
import Theorems.Thm_AvramDividend_Classical_negative_levy_compensated_primitive_integrable
import Theorems.Thm_AvramDividend_Classical_negative_levy_tail_finite_of_quadratic
import Theorems.Thm_AvramDividend_Classical_original_negative_mark_compensation_outer_measure
import Theorems.Thm_AvramDividend_Classical_negative_levy_real_tail_tonelli_outer_measure
set_option autoImplicit false
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hσ : X.σ = 0) (θ : ℝ) (hθ : 0 < θ) :
    IntegrableOn
      (fun t : ℝ => (1 - Real.exp (-θ * t)) * (X.ν (Iio (-t))).toReal)
      (Ioi (0 : ℝ)) ∧
    X.ψ θ / θ =
      X.c + (∫ y in Iic (-1 : ℝ), y ∂X.ν) +
      (∫ t in Ioi (0 : ℝ),
        (1 - Real.exp (-θ * t)) * (X.ν (Iio (-t))).toReal) := by
  have hLarge :=
    avram_ja18g_original_large_negative_signed_mark_integrable X hX
  have hFn := negative_levy_compensated_primitive_integrable
    X.ν X.ν_Ici X.ν_integrable hLarge θ hθ
  have hTailFin := negative_levy_tail_finite_of_quadratic
    X.ν X.ν_integrable
  have hTail := negative_levy_real_tail_tonelli_outer_measure
    X.ν X.ν_Ici hTailFin θ hθ hFn
  have hMark := original_negative_mark_compensation_outer_measure
    X.ν X.ν_Ici θ hθ hLarge hFn
  have hν : X.ν.restrict (Iio (0 : ℝ)) = X.ν := by
    apply Measure.restrict_eq_self_of_ae_mem
    filter_upwards [measure_eq_zero_iff_ae_notMem.mp X.ν_Ici] with y hy
    exact lt_of_not_ge (by simpa only [mem_Ici] using hy)
  have hPsi : X.ψ θ =
      X.c * θ + ∫ y : ℝ,
        (Real.exp (θ * y) - 1 -
          θ * y * (Ioo (-1 : ℝ) 1).indicator 1 y) ∂X.ν := by
    simp [SpectrallyNegativeLevy.ψ, laplaceExponent, hσ, hν]
  refine ⟨hTail.1, ?_⟩
  rw [hPsi, hMark, hTail.2]
  have hθ0 : θ ≠ 0 := ne_of_gt hθ
  field_simp [hθ0]
  ring
