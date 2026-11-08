-- Prove2me | solution 1 for AvramDividend.Classical.avram_bv_jump8_cadlag_weighted_exact_candidate_enumeration
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-07T08:56:29.468205+00:00
-- url     : https://prove2.me/submissions/443ac39a-a5f5-48b8-8ba3-3827fc11d57a

import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Theorems.Thm_AvramDividend_Classical_avram_bv_jump8_turn9_measurable_exact_cadlag_selectors
import Theorems.Thm_AvramDividend_Classical_avram_bv_jump8_turn9_weighted_candidate_count_identity
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section
attribute [local instance] Classical.propDecidable

/-- Deduplicated weighted càdlàg candidate extraction using two proved children. -/
theorem solution
    (T : ℝ≥0) (g : ℝ → ℝ≥0∞) (hg : Measurable g) :
    ∃ (time : ℕ → (ℝ≥0 → ℝ) → ℝ≥0)
      (mark : ℕ → (ℝ≥0 → ℝ) → ℝ),
      (∀ k, Measurable (time k)) ∧
      (∀ k, Measurable (mark k)) ∧
      ∀ Y : ℝ≥0 → ℝ,
        (∀ u : ℝ≥0, ContinuousWithinAt Y (Ici u) u) →
        (∀ u : ℝ≥0, 0 < u → ∃ l : ℝ, Tendsto Y (𝓝[<] u) (𝓝 l)) →
        (∑' k : ℕ,
          if 0 < time k Y ∧ time k Y ≤ T ∧
              (∀ j : ℕ, j < k → time j Y ≠ time k Y)
          then (if mark k Y = 0 then 0 else g (mark k Y))
          else 0) =
        ∫⁻ p : ℝ≥0 × ℝ,
          if 0 < p.1 ∧ p.1 ≤ T then g p.2 else 0 ∂
          ((Measure.count.restrict {u : ℝ≥0 |
            0 < u ∧ Y u - Function.leftLim Y u ≠ 0}).map
            (fun u => (u, Y u - Function.leftLim Y u))) := by
  obtain ⟨time, mark, hTime, hMark, hExact⟩ :=
    avram_bv_jump8_turn9_measurable_exact_cadlag_selectors
  refine ⟨time, mark, hTime, hMark, ?_⟩
  intro Y hRight hLeft
  have hCount :=
    avram_bv_jump8_turn9_weighted_candidate_count_identity
      T g hg time mark hExact Y hRight hLeft
  convert hCount using 1
