-- Prove2me | solution 1 for AvramDividend.Classical.avram_ja18p1a_laplace_controls_large_tail
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-11T01:56:02.993049+00:00
-- url     : https://prove2.me/submissions/02d01aa5-787d-4684-8bc3-3fd52abbbbc8

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_ja18p1a1_original_large_tail_laplace_split
import Theorems.Thm_AvramDividend_Classical_avram_ja18p1a2_uniform_small_exp_remainder_rate

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

/-- Signed original Levy split plus uniform small-jump remainder bound controls the large tail. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) :
    ∃ D : ℝ, ∀ θ : ℝ, 0 < θ → θ ≤ 1 →
      (∫⁻ z in Iic (-1 : ℝ),
        ENNReal.ofReal ((1 - Real.exp (θ * z)) / θ) ∂X.ν) ≤
        ENNReal.ofReal (D - laplaceExponent X.c X.σ X.ν θ / θ) := by
  obtain ⟨K, hSmall⟩ :=
    avram_ja18p1a2_uniform_small_exp_remainder_rate X
  refine ⟨X.c + X.σ ^ 2 / 2 + K, ?_⟩
  intro θ hθ hθOne
  rw [avram_ja18p1a1_original_large_tail_laplace_split
    X θ hθ hθOne]
  apply ENNReal.ofReal_le_ofReal
  have hσ : 0 ≤ X.σ ^ 2 := sq_nonneg X.σ
  have hσBound : X.σ ^ 2 * θ ≤ X.σ ^ 2 := by
    have h := mul_le_mul_of_nonneg_left hθOne hσ
    nlinarith
  linarith [hSmall θ hθ hθOne]
