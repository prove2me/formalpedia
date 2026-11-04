-- Prove2me | solution 1 for AvramDividend.Classical.avram_p2_e_compensator_finite_predictable_simple_weighted_rate
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T12:08:43.134731+00:00
-- url     : https://prove2.me/submissions/7eed71ec-9ff0-4beb-8416-b8432c708306

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p2_e_compensator_intrinsic_rectangle_count_measurable
import Theorems.Thm_AvramDividend_Classical_avram_p2_e_compensator_weighted_rate_from_unconditional

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal BigOperators

/-- Finite sums of genuine original-process predictable rectangular jump costs
admit the prescribed compensator from separately established unconditional rates;
the time, mark and past-measurable nonnegative weight may vary with each step. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    {ι : Type*} (S : Finset ι)
    (s t : ι → ℝ≥0) (hst : ∀ i ∈ S, s i ≤ t i)
    (B : ι → Set ℝ) (hB : ∀ i ∈ S, MeasurableSet (B i))
    (W : ι → Ω → ℝ≥0∞)
    (hW : ∀ i ∈ S, Measurable[𝓕 (s i)] (W i))
    (hRate : ∀ i ∈ S,
      (∫⁻ ω, ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u,
          X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
        (Ioc (s i) (t i) ×ˢ B i) ∂P) =
        ((t i - s i : ℝ≥0) : ℝ≥0∞) * X.ν (B i)) :
    (∫⁻ ω, ∑ i ∈ S,
      W i ω * ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u,
          X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
        (Ioc (s i) (t i) ×ˢ B i) ∂P) =
    ∑ i ∈ S, (∫⁻ ω, W i ω ∂P) *
      (((t i - s i : ℝ≥0) : ℝ≥0∞) * X.ν (B i)) := by
  have hMeas (i : ι) (hi : i ∈ S) :
      Measurable (fun ω : Ω =>
        W i ω * ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u,
          X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
        (Ioc (s i) (t i) ×ˢ B i)) := by
    exact
      ((hW i hi).mono (𝓕.le (s i)) le_rfl).mul
        (avram_p2_e_compensator_intrinsic_rectangle_count_measurable
          X (s i) (t i) (hst i hi) (B i) (hB i hi))
  rw [lintegral_finset_sum S hMeas]
  exact Finset.sum_congr rfl (fun i hi =>
    avram_p2_e_compensator_weighted_rate_from_unconditional
      X (s i) (t i) (hst i hi) (B i) (hB i hi)
      (W i) (hW i hi) (hRate i hi))
