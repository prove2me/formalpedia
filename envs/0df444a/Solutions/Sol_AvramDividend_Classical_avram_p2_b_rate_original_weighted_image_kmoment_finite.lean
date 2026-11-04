-- Prove2me | solution 1 for AvramDividend.Classical.avram_p2_b_rate_original_weighted_image_kmoment_finite
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T21:18:51.771213+00:00
-- url     : https://prove2.me/submissions/118b72a6-6c37-4094-a316-63cf816a3b83

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p2_b_rate_original_weighted_integer_integrable
import Theorems.Thm_AvramDividend_Classical_avram_p2_b_rate_integrable_weighted_image_kmoment_finite

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hX : ∀ t : ℝ≥0, Measurable (X.X t))
    (t : ℝ≥0) (θ : ℝ) (hθ : 0 ≤ θ) (k : ℕ) :
    (∫⁻ z : ℝ, ENNReal.ofReal (z ^ k) ∂
      ((P.withDensity (fun ω =>
        ENNReal.ofReal ((Real.exp (θ * X.X t ω) - 1) ^ 4))).map
        (fun ω => Real.exp (θ * X.X t ω)))) < ⊤ := by
  have hi :=
    AvramDividend.Classical.avram_p2_b_rate_original_weighted_integer_integrable
      X t k θ hθ
  exact
    AvramDividend.Classical.avram_p2_b_rate_integrable_weighted_image_kmoment_finite
      P (X.X t) (hX t) θ k hi
