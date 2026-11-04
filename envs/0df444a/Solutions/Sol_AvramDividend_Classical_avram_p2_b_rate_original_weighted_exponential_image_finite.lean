-- Prove2me | solution 1 for AvramDividend.Classical.avram_p2_b_rate_original_weighted_exponential_image_finite
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T20:42:01.319845+00:00
-- url     : https://prove2.me/submissions/bd4abc30-44f8-4ef5-bb32-02369e9fe4fb

import Mathlib
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Map
import Mathlib.MeasureTheory.Function.SpecialFunctions.Basic
import Mathlib.MeasureTheory.Measure.WithDensity
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p2_b_rate_original_weighted_integer_integrable
import Theorems.Thm_AvramDividend_Classical_avram_p2_b_rate_integrable_nonnegative_density_finite

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
    (t : ℝ≥0) (θ : ℝ) (hθ : 0 ≤ θ) :
    (((P.withDensity (fun ω =>
      ENNReal.ofReal ((Real.exp (θ * X.X t ω) - 1) ^ 4))).map
      (fun ω => Real.exp (θ * X.X t ω))) Set.univ) < ⊤ := by
  have hInt : Integrable
      (fun ω => (Real.exp (θ * X.X t ω) - 1) ^ 4) P := by
    simpa only [pow_zero, one_mul] using
      (AvramDividend.Classical.avram_p2_b_rate_original_weighted_integer_integrable
        X t 0 θ hθ)
  have hn : ∀ᵐ ω ∂P,
      0 ≤ (Real.exp (θ * X.X t ω) - 1) ^ 4 :=
    Filter.Eventually.of_forall (fun ω => by positivity)
  have hfinite :=
    AvramDividend.Classical.avram_p2_b_rate_integrable_nonnegative_density_finite
      P (fun ω => (Real.exp (θ * X.X t ω) - 1) ^ 4) hInt hn
  have hmap : Measurable (fun ω => Real.exp (θ * X.X t ω)) :=
    (Real.measurable_exp).comp (measurable_const.mul (hX t))
  simpa only [Measure.map_apply hmap MeasurableSet.univ,
    Set.preimage_univ] using hfinite
