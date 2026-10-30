-- Prove2me | solution 1 for AvramDividend.Classical.avram_root29_01_actual_random_grid_history_meas
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-29T15:13:14.225729+00:00
-- url     : https://prove2.me/submissions/44070b98-0c91-417b-b193-78145c7d4caf

import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Mathlib.Tactic.Ring
import Theorems.Thm_AvramDividend_Classical_avram_root29_01_random_grid_killed_history_meas
import Theorems.Thm_AvramDividend_Classical_avram_root29_01_shifted_lower_closed_event_measurable

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

/-- The actual original-Levy history survival up to a measurable random
grid time is measurable, using source deterministic-clock history law. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (clock : ℕ → ℝ≥0) (K : Ω → ℕ)
    (hKm : Measurable K) :
    MeasurableSet {ω : Ω | ∀ t : ℝ≥0,
      t ≤ clock (K ω) → 0 ≤ x + X.X t ω} := by
  have hFixed (k : ℕ) : MeasurableSet
      {ω : Ω | ∀ t : ℝ≥0, t ≤ clock k →
        0 ≤ x + X.X t ω} := by
    have h0 := avram_root29_01_shifted_lower_closed_event_measurable
      X x 0 (clock k)
    have hEq :
        {ω : Ω | ∀ t : ℝ≥0, t ≤ clock k →
          0 ≤ (x + X.X 0 ω) + (X.X (0 + t) ω - X.X 0 ω)} =
        {ω : Ω | ∀ t : ℝ≥0, t ≤ clock k →
          0 ≤ x + X.X t ω} := by
      ext ω
      simp only [Set.mem_setOf_eq, zero_add]
      constructor
      · intro h t ht
        convert h t ht using 1 <;> ring
      · intro h t ht
        convert h t ht using 1 <;> ring
    rw [hEq] at h0
    exact h0
  exact avram_root29_01_random_grid_killed_history_meas
    X x clock K hKm hFixed
