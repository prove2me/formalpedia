-- Prove2me | solution 1 for AvramDividend.Classical.avram_p3_grid3_original_ruin_stopped_positive_tau_has_crossing_cell
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-05T19:16:32.1312+00:00
-- url     : https://prove2.me/submissions/89b2cf0c-56ab-4b0f-b112-82f1ca74a902

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_p3_grid3_original_ruin_stopped_uniform_physical_clock
import Theorems.Thm_AvramDividend_Classical_avram_p3_grid3_original_ruin_stopped_physical_grid_reaches_exact_tau
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- The original stopped physical clock has a crossing cell at every positive stopped time. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (x : ℝ)
    (D : ℝ≥0 → Ω → ℝ)
    (T : ℝ≥0) (m : ℕ) (ω : Ω) :
    let τ : ℝ≥0 :=
      (min (ruinTime X x D ω) (T : ℝ≥0∞)).toNNReal
    let u : ℕ → ℝ≥0 := fun j =>
      min (((min j (m + 1) : ℕ) : ℝ≥0) *
        (T / (m + 1))) τ
    0 < τ →
      ∃ i : ℕ, i < m + 1 ∧ u i < τ ∧ u (i + 1) = τ := by
  let τ : ℝ≥0 :=
    (min (ruinTime X x D ω) (T : ℝ≥0∞)).toNNReal
  let u : ℕ → ℝ≥0 := fun j =>
    min (((min j (m + 1) : ℕ) : ℝ≥0) *
      (T / (m + 1))) τ
  change 0 < τ → ∃ i : ℕ, i < m + 1 ∧
    u i < τ ∧ u (i + 1) = τ
  intro hτ
  have h0 : u 0 = 0 :=
    (avram_p3_grid3_original_ruin_stopped_uniform_physical_clock
      X x D T m ω).1
  have hlast : u (m + 1) = τ :=
    avram_p3_grid3_original_ruin_stopped_physical_grid_reaches_exact_tau
      X x D T m ω
  have haux : ∀ n : ℕ, u 0 < τ → u (n + 1) = τ →
      ∃ i : ℕ, i ≤ n ∧ u i < τ ∧ u (i + 1) = τ := by
    intro n
    induction n with
    | zero =>
        intro hz hn
        exact ⟨0, by omega, hz, hn⟩
    | succ n ih =>
        intro hz hn
        by_cases hp : u (n + 1) < τ
        · exact ⟨n + 1, by omega, hp, hn⟩
        · have hle : u (n + 1) ≤ τ := by
            change min (((min (n + 1) (m + 1) : ℕ) : ℝ≥0) *
              (T / (m + 1))) τ ≤ τ
            exact min_le_right _ _
          have heq : u (n + 1) = τ :=
            le_antisymm hle (le_of_not_gt hp)
          obtain ⟨i, hi, hlt, hit⟩ := ih hz heq
          exact ⟨i, by omega, hlt, hit⟩
  have hz : u 0 < τ := by simpa only [h0] using hτ
  obtain ⟨i, hi, hlt, hit⟩ := haux m hz hlast
  exact ⟨i, by omega, hlt, hit⟩
