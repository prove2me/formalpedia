-- Prove2me | solution 1 for AvramDividend.Classical.avram_p3_grid3_original_ruin_stopped_strict_prefix_card_eq_crossing_index
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-05T19:37:40.113196+00:00
-- url     : https://prove2.me/submissions/211f6285-ff94-49f9-89c2-e6450826ddd0

import Mathlib.Probability.Process.Filtration
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_p3_grid3_original_ruin_stopped_positive_tau_has_crossing_cell
import Theorems.Thm_AvramDividend_Classical_avram_p3_grid3_original_ruin_stopped_uniform_physical_clock
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- The explicit source-exact strict-prefix cardinal equals the unique crossing-cell index. -/
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
    let k : ℕ :=
      ((Finset.range (m + 1)).filter
        (fun j => u (j + 1) < τ)).card
    0 < τ →
      ∃ i : ℕ, i < m + 1 ∧ u i < τ ∧
        u (i + 1) = τ ∧ k = i := by
  classical
  let τ : ℝ≥0 :=
    (min (ruinTime X x D ω) (T : ℝ≥0∞)).toNNReal
  let u : ℕ → ℝ≥0 := fun j =>
    min (((min j (m + 1) : ℕ) : ℝ≥0) *
      (T / (m + 1))) τ
  let k : ℕ :=
    ((Finset.range (m + 1)).filter
      (fun j => u (j + 1) < τ)).card
  change 0 < τ →
    ∃ i : ℕ, i < m + 1 ∧ u i < τ ∧ u (i + 1) = τ ∧ k = i
  intro hτ
  obtain ⟨i, hi, hbelow, hhit⟩ :=
    avram_p3_grid3_original_ruin_stopped_positive_tau_has_crossing_cell
      X x D T m ω hτ
  have hu : Monotone u :=
    (avram_p3_grid3_original_ruin_stopped_uniform_physical_clock
      X x D T m ω).2.2
  have hfilter : (Finset.range (m + 1)).filter
      (fun j => u (j + 1) < τ) = Finset.range i := by
    ext j
    simp only [Finset.mem_filter, Finset.mem_range]
    constructor
    · intro ⟨hj, hlt⟩
      by_contra hji
      have hle : i + 1 ≤ j + 1 := by omega
      have hbig : τ ≤ u (j + 1) := by
        have hleft : τ ≤ u (i + 1) := le_of_eq hhit.symm
        exact hleft.trans (hu hle)
      exact (not_lt_of_ge hbig) hlt
    · intro hj
      have hjle : j + 1 ≤ i := by omega
      exact ⟨by omega, lt_of_le_of_lt (hu hjle) hbelow⟩
  have hk : k = i := by
    dsimp [k]
    rw [hfilter]
    simp
  exact ⟨i, hi, hbelow, hhit, hk⟩
