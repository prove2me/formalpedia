-- Prove2me | solution 1 for AvramDividend.Classical.chat04_closed_horizon_dense_survival_eq
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-20T10:16:16.139596+00:00
-- url     : https://prove2.me/submissions/367d3875-7f11-4887-94f3-e80e375c79ad

import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_chat04_finite_horizon_dense_schedule_survival_eq
import Mathlib.MeasureTheory.MeasurableSpace.Defs

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

/-!
The correct closed-horizon survival event is the dense-grid no-exit event
BEFORE T together with a separate observation at T. This avoids any
assumption that Lévy paths cannot first exit at a deterministic horizon.
-/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (τ : ℕ → ℝ≥0)
    (hCover : ∀ n : ℕ, 0 < n → ∀ k : ℕ,
      ∃ j : ℕ, τ j = (k : ℝ≥0) * (n : ℝ≥0)⁻¹)
    (lower upper : ℝ) (T : ℝ≥0) :
    {ω | ∀ t : ℝ≥0, t ≤ T →
      ¬ (X.X t ω < lower ∨ upper < X.X t ω)} =
      (⋂ j : ℕ, {ω | τ j < T →
        ¬ (X.X (τ j) ω < lower ∨ upper < X.X (τ j) ω)}) ∩
        {ω | ¬ (X.X T ω < lower ∨ upper < X.X T ω)} := by
  have hBefore :
      {ω | ∀ t : ℝ≥0, t < T →
        ¬ (X.X t ω < lower ∨ upper < X.X t ω)} =
        ⋂ j : ℕ, {ω | τ j < T →
          ¬ (X.X (τ j) ω < lower ∨ upper < X.X (τ j) ω)} :=
    AvramDividend.Classical.chat04_finite_horizon_dense_schedule_survival_eq
      X τ hCover lower upper T
  ext ω
  simp only [Set.mem_setOf_eq, Set.mem_inter_iff, Set.mem_iInter]
  constructor
  · intro h
    constructor
    · intro j hj
      exact h (τ j) (le_of_lt hj)
    · exact h T le_rfl
  · rintro ⟨hGrid, hT⟩ t ht
    by_cases hlt : t < T
    · have hGridSet : ω ∈
          (⋂ j : ℕ, {ω | τ j < T →
            ¬ (X.X (τ j) ω < lower ∨ upper < X.X (τ j) ω)}) := by
        simpa only [Set.mem_iInter, Set.mem_setOf_eq] using hGrid
      rw [← hBefore] at hGridSet
      exact hGridSet t hlt
    · have htEq : t = T :=
        le_antisymm ht (le_of_not_gt hlt)
      subst t
      exact hT
