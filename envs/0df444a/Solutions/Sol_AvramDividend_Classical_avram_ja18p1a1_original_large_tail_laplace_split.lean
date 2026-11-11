-- Prove2me | solution 1 for AvramDividend.Classical.avram_ja18p1a1_original_large_tail_laplace_split
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-11T02:03:24.652044+00:00
-- url     : https://prove2.me/submissions/c488c79e-156e-4507-b7e1-cce306184b97

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_ja18p1a1a_original_levy_exponent_integral_split
import Theorems.Thm_AvramDividend_Classical_avram_ja18p1a1b_large_exp_lintegral_real_bridge

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

/-- The original Levy exponent integral split identifies the exact large-mark exponential loss. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (θ : ℝ) (hθ : 0 < θ) (hθOne : θ ≤ 1) :
    (∫⁻ z in Iic (-1 : ℝ),
        ENNReal.ofReal ((1 - Real.exp (θ * z)) / θ) ∂X.ν) =
      ENNReal.ofReal
        (X.c + X.σ ^ 2 * θ / 2 +
          (∫ z in Ioo (-1 : ℝ) 0,
            (Real.exp (θ * z) - 1 - θ * z) ∂X.ν) / θ -
          laplaceExponent X.c X.σ X.ν θ / θ) := by
  rw [avram_ja18p1a1b_large_exp_lintegral_real_bridge X θ hθ]
  congr 1
  unfold laplaceExponent
  rw [avram_ja18p1a1a_original_levy_exponent_integral_split X θ hθ.le]
  field_simp [ne_of_gt hθ]
  ring
