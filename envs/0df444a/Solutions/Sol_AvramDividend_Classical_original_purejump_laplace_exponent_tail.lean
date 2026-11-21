-- Prove2me | solution 1 for AvramDividend.Classical.original_purejump_laplace_exponent_tail
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-20T19:54:51.323056+00:00
-- url     : https://prove2.me/submissions/065fbc54-c50b-4898-8f84-e365b64da324
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_ja18g_original_large_negative_signed_mark_integrable
import Theorems.Thm_AvramDividend_Classical_negative_levy_tail_real_integral_bridge
import Theorems.Thm_AvramDividend_Classical_original_purejump_lk_mark_decomposition
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
  have hBridge := negative_levy_tail_real_integral_bridge
    X.ν X.ν_Ici X.ν_integrable
    (avram_ja18g_original_large_negative_signed_mark_integrable X hX)
    θ hθ
  refine ⟨hBridge.2.1, ?_⟩
  calc
    X.ψ θ / θ =
      X.c + (∫ y in Iic (-1 : ℝ), y ∂X.ν) +
      (∫ y : ℝ, ∫ t in (0 : ℝ)..(-y),
        1 - Real.exp (-θ * t) ∂X.ν) :=
      original_purejump_lk_mark_decomposition
        X hX hσ θ hθ hBridge.1
    _ = X.c + (∫ y in Iic (-1 : ℝ), y ∂X.ν) +
      (∫ t in Ioi (0 : ℝ),
        (1 - Real.exp (-θ * t)) * (X.ν (Iio (-t))).toReal) := by
      rw [hBridge.2.2]
