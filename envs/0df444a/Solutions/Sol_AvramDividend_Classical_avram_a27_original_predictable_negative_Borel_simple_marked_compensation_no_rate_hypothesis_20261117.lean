-- Prove2me | solution 1 for AvramDividend.Classical.avram_a27_original_predictable_negative_Borel_simple_marked_compensation_no_rate_hypothesis_20261117
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-17T17:09:31.777303+00:00
-- url     : https://prove2.me/submissions/687392d4-a23a-4823-aa1e-670279d0f98b

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p2_e_compensator_finite_predictable_simple_weighted_rate
import Theorems.Thm_AvramDividend_Classical_avram_b24_original_negative_Borel_marked_Poisson_interval_Campbell_exact

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal BigOperators
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    {ι : Type*} (S : Finset ι)
    (s t : ι → ℝ≥0) (hst : ∀ i ∈ S, s i ≤ t i)
    (B : ι → Set ℝ) (hB : ∀ i ∈ S, MeasurableSet (B i))
    (W : ι → Ω → ℝ≥0∞)
    (hW : ∀ i ∈ S, Measurable[𝓕 (s i)] (W i))
    (hNeg : ∀ i ∈ S, B i ⊆ Iio (0 : ℝ)) :
    (∫⁻ ω, ∑ i ∈ S,
      W i ω * ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u,
          X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
        (Ioc (s i) (t i) ×ˢ B i) ∂P) =
    ∑ i ∈ S, (∫⁻ ω, W i ω ∂P) *
      (((t i - s i : ℝ≥0) : ℝ≥0∞) * X.ν (B i)) := by
  apply avram_p2_e_compensator_finite_predictable_simple_weighted_rate
    X S s t hst B hB W hW
  intro i hi
  exact avram_b24_original_negative_Borel_marked_Poisson_interval_Campbell_exact
    X (s i) (t i) (hst i hi) (B i) (hB i hi) (hNeg i hi)
