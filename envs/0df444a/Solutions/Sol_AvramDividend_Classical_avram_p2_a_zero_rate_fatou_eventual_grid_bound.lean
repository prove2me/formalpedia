-- Prove2me | solution 1 for AvramDividend.Classical.avram_p2_a_zero_rate_fatou_eventual_grid_bound
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T10:50:31.845196+00:00
-- url     : https://prove2.me/submissions/0c15d9ed-c7ed-46f7-b1ad-cd8ed01942b2

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_p2_grid_count_pathwise_liminf_implies_expected_liminf

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal

/-- A pathwise grid-count liminf and an eventual expected-grid bound
give a finite upper bound on the original mean count by Fatou. -/
theorem solution
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (jumpCount : Ω → ℝ≥0∞) (grid : ℕ → Ω → ℝ≥0∞)
    (hgrid : ∀ n, Measurable (grid n))
    (hPoint : ∀ ω, jumpCount ω ≤
      Filter.liminf (fun n => grid n ω) Filter.atTop)
    (M : ℝ≥0∞)
    (hBound : ∀ᶠ n : ℕ in Filter.atTop,
      (∫⁻ ω, grid n ω ∂P) ≤ M) :
    (∫⁻ ω, jumpCount ω ∂P) ≤ M := by
  have hFatou :=
    avram_p2_grid_count_pathwise_liminf_implies_expected_liminf
      P jumpCount grid hgrid hPoint
  apply hFatou.trans
  refine Filter.liminf_le_of_le (hf := by isBoundedDefault) ?_
  intro b hb
  obtain ⟨n, hbn, hnM⟩ := (hb.and hBound).exists
  exact hbn.trans hnM
