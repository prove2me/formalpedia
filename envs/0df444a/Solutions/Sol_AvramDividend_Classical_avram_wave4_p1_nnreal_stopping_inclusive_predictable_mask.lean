-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave4_p1_nnreal_stopping_inclusive_predictable_mask
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-31T19:23:16.453982+00:00
-- url     : https://prove2.me/submissions/4f65e090-0a83-4efc-8364-144e28adfc00

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_wave4_p1_countable_time_stopping_inclusive_predictable_mask

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal

/-- The inclusive stopped survival mask is predictable for an actual
filtration on nonnegative real time, with no separability hypothesis left
for the stochastic applications. Countable nonnegative rational times form
the separating family, including when the stop happens between grid cells. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    (𝓕 : Filtration ℝ≥0 mΩ)
    (τ : Ω → ℝ≥0)
    (hτ : IsStoppingTime 𝓕 (fun ω => (τ ω : WithTop ℝ≥0))) :
    MeasurableSet[𝓕.predictable]
      {p : ℝ≥0 × Ω | p.1 ≤ τ p.2} := by
  classical
  let D : Set ℝ≥0 := Set.range (fun q : ℚ => Real.toNNReal q)
  have hD : D.Countable := Set.countable_range _
  have hSep : ∀ a b : ℝ≥0, a < b →
      ∃ s : ℝ≥0, s ∈ D ∧ a ≤ s ∧ s < b := by
    intro a b hab
    obtain ⟨q, hq0, haq, hqb⟩ :=
      (NNReal.lt_iff_exists_rat_btwn a b).mp hab
    exact ⟨Real.toNNReal q, ⟨q, rfl⟩, le_of_lt haq, hqb⟩
  exact AvramDividend.Classical.avram_wave4_p1_countable_time_stopping_inclusive_predictable_mask
    𝓕 D hD hSep τ hτ