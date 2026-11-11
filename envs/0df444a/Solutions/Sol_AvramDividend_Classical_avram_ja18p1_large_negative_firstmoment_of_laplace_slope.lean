-- Prove2me | solution 1 for AvramDividend.Classical.avram_ja18p1_large_negative_firstmoment_of_laplace_slope
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-11T01:34:54.998348+00:00
-- url     : https://prove2.me/submissions/8a13743f-24f7-481b-9c50-40507b1a2986

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_ja18p1a_laplace_controls_large_tail
import Theorems.Thm_AvramDividend_Classical_avram_ja18p1b_fatou_large_negative_tail

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

/-- Uniform negative-tail bounds from the original exponent yield the large-jump first moment by Fatou. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (C : ℝ)
    (hSlope : ∀ θ : ℝ, 0 < θ → θ ≤ 1 →
      -C ≤ laplaceExponent X.c X.σ X.ν θ / θ) :
    (∫⁻ z in Iic (-1 : ℝ), ENNReal.ofReal |z| ∂X.ν) < ⊤ := by
  obtain ⟨D, hTail⟩ :=
    avram_ja18p1a_laplace_controls_large_tail X
  apply avram_ja18p1b_fatou_large_negative_tail X.ν (D + C)
  intro θ hθ hθOne
  calc
    (∫⁻ z in Iic (-1 : ℝ),
        ENNReal.ofReal ((1 - Real.exp (θ * z)) / θ) ∂X.ν) ≤
        ENNReal.ofReal
          (D - laplaceExponent X.c X.σ X.ν θ / θ) :=
      hTail θ hθ hθOne
    _ ≤ ENNReal.ofReal (D + C) := by
      apply ENNReal.ofReal_le_ofReal
      linarith [hSlope θ hθ hθOne]
