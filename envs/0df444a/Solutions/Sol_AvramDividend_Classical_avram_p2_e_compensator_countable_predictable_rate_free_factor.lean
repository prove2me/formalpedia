-- Prove2me | solution 1 for AvramDividend.Classical.avram_p2_e_compensator_countable_predictable_rate_free_factor
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T13:06:17.489302+00:00
-- url     : https://prove2.me/submissions/758c3995-5656-474e-b94d-f8099a1b0396

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p2_e_compensator_intrinsic_rectangle_count_measurable
import Theorems.Thm_AvramDividend_Classical_avram_p2_e_compensator_weighted_intrinsic_rectangle_factor

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal BigOperators

/-- Countably many true-source predictable marked rectangular counts
factor from their past weights without a Levy ν-rate hypothesis. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (s t : ℕ → ℝ≥0) (hst : ∀ i, s i ≤ t i)
    (B : ℕ → Set ℝ) (hB : ∀ i, MeasurableSet (B i))
    (W : ℕ → Ω → ℝ≥0∞)
    (hW : ∀ i, Measurable[𝓕 (s i)] (W i)) :
    (∫⁻ ω, ∑' i, W i ω * ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u,
          X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
        (Ioc (s i) (t i) ×ˢ B i) ∂P) =
    ∑' i, (∫⁻ ω, W i ω ∂P) * (∫⁻ ω, ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u,
          X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
        (Ioc (s i) (t i) ×ˢ B i) ∂P) := by
  have hMeas (i : ℕ) :
      Measurable (fun ω : Ω => W i ω * ((Measure.count.restrict {u : ℝ≥0 |
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
    avram_p2_e_compensator_weighted_intrinsic_rectangle_factor
      X (s i) (t i) (hst i) (B i) (hB i)
      (W i) (hW i))
