-- Prove2me | solution 1 for AvramDividend.Classical.avram_bv_jump8_cadlag_mark_weight_lintegral_borel
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-07T00:33:13.498193+00:00
-- url     : https://prove2.me/submissions/0ca2bbbf-0328-419e-9d04-cba99d79b9a7

import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Theorems.Thm_AvramDividend_Classical_avram_bv_jump8_measurable_deduplicated_weighted_mark_series
import Theorems.Thm_AvramDividend_Classical_avram_bv_jump8_cadlag_weighted_exact_candidate_enumeration

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section
attribute [local instance] Classical.propDecidable

/-- Recover the actual càdlàg marked weighted integral from measurable selectors. -/
theorem solution
    (T : ℝ≥0) (g : ℝ → ℝ≥0∞) (hg : Measurable g) :
    ∃ W : (ℝ≥0 → ℝ) → ℝ≥0∞,
      Measurable W ∧
      ∀ Y : ℝ≥0 → ℝ,
        (∀ u : ℝ≥0, ContinuousWithinAt Y (Ici u) u) →
        (∀ u : ℝ≥0, 0 < u → ∃ l : ℝ, Tendsto Y (𝓝[<] u) (𝓝 l)) →
        W Y =
          ∫⁻ p : ℝ≥0 × ℝ,
            if 0 < p.1 ∧ p.1 ≤ T then g p.2 else 0 ∂
              ((Measure.count.restrict {u : ℝ≥0 |
                0 < u ∧ Y u - Function.leftLim Y u ≠ 0}).map
                (fun u : ℝ≥0 => (u, Y u - Function.leftLim Y u))) := by
  obtain ⟨time, mark, hTime, hMark, hExact⟩ :=
    avram_bv_jump8_cadlag_weighted_exact_candidate_enumeration T g hg
  let g₀ : ℝ → ℝ≥0∞ := fun y =>
    if y = 0 then 0 else g y
  have hg₀ : Measurable g₀ := by
    change Measurable (fun y : ℝ => if y = 0 then (0 : ℝ≥0∞) else g y)
    exact Measurable.ite
      (measurableSet_singleton (0 : ℝ))
      measurable_const hg
  let W : (ℝ≥0 → ℝ) → ℝ≥0∞ := fun Y =>
    ∑' k : ℕ,
      if 0 < time k Y ∧ time k Y ≤ T ∧
          (∀ j : ℕ, j < k → time j Y ≠ time k Y)
      then g₀ (mark k Y) else 0
  refine ⟨W, ?_, ?_⟩
  · exact avram_bv_jump8_measurable_deduplicated_weighted_mark_series
      time mark hTime hMark T g₀ hg₀
  · intro Y hRight hLeft
    simpa only [W, g₀] using hExact Y hRight hLeft
