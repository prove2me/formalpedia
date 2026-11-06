-- Prove2me | solution 1 for AvramDividend.Classical.avram_p3_grid3_original_ruin_stopped_positive_tau_boundary_filter_singleton
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-05T19:20:38.3642+00:00
-- url     : https://prove2.me/submissions/73a5eb88-f969-4077-b093-a96ae253f91a

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_p3_grid3_original_ruin_stopped_positive_tau_has_crossing_cell
import Theorems.Thm_AvramDividend_Classical_avram_p3_grid3_original_ruin_stopped_physical_unique_crossing
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- The actual stopped physical-grid boundary filter contains its unique positive-time crossing. -/
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
      ∃ i : ℕ, i < m + 1 ∧ u i < τ ∧ u (i + 1) = τ ∧
        (Finset.range (m + 1)).filter
          (fun j => u j < τ ∧ u (j + 1) = τ) =
            ({i} : Finset ℕ) := by
  classical
  let τ : ℝ≥0 :=
    (min (ruinTime X x D ω) (T : ℝ≥0∞)).toNNReal
  let u : ℕ → ℝ≥0 := fun j =>
    min (((min j (m + 1) : ℕ) : ℝ≥0) *
      (T / (m + 1))) τ
  change 0 < τ →
    ∃ i : ℕ, i < m + 1 ∧ u i < τ ∧ u (i + 1) = τ ∧
      (Finset.range (m + 1)).filter
        (fun j => u j < τ ∧ u (j + 1) = τ) =
          ({i} : Finset ℕ)
  intro hτ
  obtain ⟨i, hi, hbelow, hhit⟩ :=
    avram_p3_grid3_original_ruin_stopped_positive_tau_has_crossing_cell
      X x D T m ω hτ
  have hunique :=
    avram_p3_grid3_original_ruin_stopped_physical_unique_crossing
      X x D T m ω
  refine ⟨i, hi, hbelow, hhit, ?_⟩
  apply Finset.ext
  intro j
  simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_singleton]
  constructor
  · intro ⟨hj, hjbelow, hjhit⟩
    rcases lt_trichotomy i j with hij | hijeq | hji
    · exact False.elim ((hunique i j hij hbelow hhit)
        ⟨hjbelow, hjhit⟩)
    · exact hijeq.symm
    · exact False.elim ((hunique j i hji hjbelow hjhit)
        ⟨hbelow, hhit⟩)
  · intro hji
    subst j
    exact ⟨hi, hbelow, hhit⟩
