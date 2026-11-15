-- Prove2me | solution 1 for AvramDividend.Classical.counting_delta_unif_integrable
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-14T10:35:44.745724+00:00
-- url     : https://prove2.me/submissions/5614bf07-b66a-453f-933e-3845ded73089

import Mathlib
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter Set
open scoped ENNReal
noncomputable section
theorem solution :
    UnifIntegrable (fun n : ℕ => ({n} : Set ℕ).indicator
      (fun _ => (1 : ℝ))) 1 (Measure.count : Measure ℕ) := by
  intro ε hε
  refine ⟨ε, hε, ?_⟩
  intro n s hs hμs
  have hpoint : ∀ ω : ℕ,
      ‖s.indicator (({n} : Set ℕ).indicator (fun _ => (1 : ℝ))) ω‖ ≤
      ‖s.indicator (fun _ : ℕ => (1 : ℝ)) ω‖ := by
    intro ω
    by_cases hω : ω ∈ s
    · simp only [Set.indicator_of_mem hω]
      by_cases hn : ω = n
      · simp [hn]
      · simp [Set.indicator, hn]
    · simp [Set.indicator_of_notMem hω]
  have hle := eLpNorm_mono (p := (1 : ℝ≥0∞))
    (μ := (Measure.count : Measure ℕ)) hpoint
  have hconst : eLpNorm (s.indicator (fun _ : ℕ => (1 : ℝ))) 1
      (Measure.count : Measure ℕ) = (Measure.count : Measure ℕ) s := by
    rw [eLpNorm_indicator_const hs (by norm_num) (by norm_num)]
    simp
  rw [hconst] at hle
  exact hle.trans hμs
