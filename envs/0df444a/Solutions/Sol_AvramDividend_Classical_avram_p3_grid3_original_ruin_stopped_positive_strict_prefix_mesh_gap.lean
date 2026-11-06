-- Prove2me | solution 1 for AvramDividend.Classical.avram_p3_grid3_original_ruin_stopped_positive_strict_prefix_mesh_gap
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-05T19:46:20.198135+00:00
-- url     : https://prove2.me/submissions/838b92de-ee7f-4ff7-93ed-6d19675b0f6e

import Mathlib.Probability.Process.Filtration
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_p3_grid3_original_ruin_stopped_positive_tau_has_crossing_cell
import Theorems.Thm_AvramDividend_Classical_avram_p3_grid3_original_ruin_stopped_physical_cell_length_le
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- The strictly pre-ruin last physical node is within one deterministic mesh step of tau. -/
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
      ∃ i : ℕ, i < m + 1 ∧ u i < τ ∧
        u (i + 1) = τ ∧ τ - u i ≤ T / (m + 1) := by
  let τ : ℝ≥0 :=
    (min (ruinTime X x D ω) (T : ℝ≥0∞)).toNNReal
  let u : ℕ → ℝ≥0 := fun j =>
    min (((min j (m + 1) : ℕ) : ℝ≥0) *
      (T / (m + 1))) τ
  change 0 < τ →
    ∃ i : ℕ, i < m + 1 ∧ u i < τ ∧
      u (i + 1) = τ ∧ τ - u i ≤ T / (m + 1)
  intro hτ
  obtain ⟨i, hi, hbelow, hhit⟩ :=
    avram_p3_grid3_original_ruin_stopped_positive_tau_has_crossing_cell
      X x D T m ω hτ
  have hlen :=
    avram_p3_grid3_original_ruin_stopped_physical_cell_length_le
      X x D T m i hi ω
  change u (i + 1) - u i ≤ T / (m + 1) at hlen
  have hgap : τ - u i ≤ T / (m + 1) := calc
    τ - u i = u (i + 1) - u i :=
      congrArg (fun z : ℝ≥0 => z - u i) hhit.symm
    _ ≤ T / (m + 1) := hlen
  exact ⟨i, hi, hbelow, hhit, hgap⟩
