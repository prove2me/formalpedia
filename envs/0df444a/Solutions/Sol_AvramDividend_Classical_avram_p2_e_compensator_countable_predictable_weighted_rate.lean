-- Prove2me | solution 1 for AvramDividend.Classical.avram_p2_e_compensator_countable_predictable_weighted_rate
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T12:09:23.650474+00:00
-- url     : https://prove2.me/submissions/d4b9755a-42b5-48e4-9df5-a9cae344e489

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p2_e_compensator_intrinsic_rectangle_count_measurable
import Theorems.Thm_AvramDividend_Classical_avram_p2_e_compensator_weighted_rate_from_unconditional

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal BigOperators

/-- Countable nonnegative original-process predictable rectangular jump costs
commute with genuine expectation, conditional only on their separate ν-rates. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (s t : ℕ → ℝ≥0) (hst : ∀ i, s i ≤ t i)
    (B : ℕ → Set ℝ) (hB : ∀ i, MeasurableSet (B i))
    (W : ℕ → Ω → ℝ≥0∞)
    (hW : ∀ i, Measurable[𝓕 (s i)] (W i))
    (hRate : ∀ i,
      (∫⁻ ω, ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u,
          X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
        (Ioc (s i) (t i) ×ˢ B i) ∂P) =
        ((t i - s i : ℝ≥0) : ℝ≥0∞) * X.ν (B i)) :
    (∫⁻ ω, ∑' i,
      W i ω * ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u,
          X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
        (Ioc (s i) (t i) ×ˢ B i) ∂P) =
    ∑' i, (∫⁻ ω, W i ω ∂P) *
      (((t i - s i : ℝ≥0) : ℝ≥0∞) * X.ν (B i)) := by
  have hMeas (i : ℕ) :
      Measurable (fun ω : Ω =>
        W i ω * ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u,
          X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
        (Ioc (s i) (t i) ×ˢ B i)) := by
    exact
      ((hW i).mono (𝓕.le (s i)) le_rfl).mul
        (avram_p2_e_compensator_intrinsic_rectangle_count_measurable
          X (s i) (t i) (hst i) (B i) (hB i))
  rw [lintegral_tsum (fun i => (hMeas i).aemeasurable)]
  exact tsum_congr (fun i =>
    avram_p2_e_compensator_weighted_rate_from_unconditional
      X (s i) (t i) (hst i) (B i) (hB i)
      (W i) (hW i) (hRate i))
