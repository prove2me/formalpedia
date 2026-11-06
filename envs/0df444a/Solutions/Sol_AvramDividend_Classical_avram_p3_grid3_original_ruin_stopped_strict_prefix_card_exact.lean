-- Prove2me | solution 1 for AvramDividend.Classical.avram_p3_grid3_original_ruin_stopped_strict_prefix_card_exact
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-05T19:16:43.615723+00:00
-- url     : https://prove2.me/submissions/fd3f6333-e6bf-43a8-a59f-8cb3decb6cad

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_p3_grid3_original_ruin_stopped_strict_end_cells_form_prefix
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- The strict original stopped-grid prefix has its canonical finite-cardinality index. -/
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
        (fun i => u (i + 1) < τ)).card
    k ≤ m + 1 ∧
      (Finset.range (m + 1)).filter
        (fun i => u (i + 1) < τ) = Finset.range k := by
  classical
  let τ : ℝ≥0 :=
    (min (ruinTime X x D ω) (T : ℝ≥0∞)).toNNReal
  let u : ℕ → ℝ≥0 := fun j =>
    min (((min j (m + 1) : ℕ) : ℝ≥0) *
      (T / (m + 1))) τ
  let k : ℕ :=
    ((Finset.range (m + 1)).filter
      (fun i => u (i + 1) < τ)).card
  change k ≤ m + 1 ∧
    (Finset.range (m + 1)).filter
      (fun i => u (i + 1) < τ) = Finset.range k
  obtain ⟨j, hj, hfilter⟩ :=
    avram_p3_grid3_original_ruin_stopped_strict_end_cells_form_prefix
      X x D T m ω
  have hk : k = j := by
    dsimp [k]
    rw [hfilter]
    simp
  constructor
  · simpa only [hk] using hj
  · simpa only [hk] using hfilter
