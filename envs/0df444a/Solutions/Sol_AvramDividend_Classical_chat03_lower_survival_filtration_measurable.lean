-- Prove2me | solution 1 for AvramDividend.Classical.chat03_lower_survival_filtration_measurable
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-22T10:47:34.220608+00:00
-- url     : https://prove2.me/submissions/49d66c67-339f-41e6-aeac-7b638786537a

import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_chat03_lower_before_horizon_countable_grid_iff
import Mathlib.MeasureTheory.MeasurableSpace.Defs

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal
open AvramDividend.Classical

/-!
A one-sided closed-horizon no-ruin event belongs to the terminal
filtration. Dense-grid strict downward passage handles times before T;
the separate endpoint observation handles an exit at exactly T.
-/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (τ : ℕ → ℝ≥0)
    (hCover : ∀ n : ℕ, 0 < n → ∀ k : ℕ,
      ∃ j : ℕ, τ j = (k : ℝ≥0) * (n : ℝ≥0)⁻¹)
    (lower : ℝ) (T : ℝ≥0) :
    MeasurableSet[𝓕 T]
      {ω | ∀ t : ℝ≥0, t ≤ T → ¬ X.X t ω < lower} := by
  have hEvent :
      {ω | ∀ t : ℝ≥0, t ≤ T → ¬ X.X t ω < lower} =
      (⋂ j : ℕ, {ω | τ j < T → ¬ X.X (τ j) ω < lower}) ∩
        {ω | ¬ X.X T ω < lower} := by
    ext ω
    simp only [Set.mem_setOf_eq, Set.mem_inter_iff, Set.mem_iInter]
    constructor
    · intro h
      exact ⟨(fun j hj => h (τ j) (le_of_lt hj)), h T le_rfl⟩
    · rintro ⟨hGrid, hT⟩ t ht hBad
      by_cases hlt : t < T
      · obtain ⟨n, hn, k, hkT, hkBad⟩ :=
          (chat03_lower_before_horizon_countable_grid_iff
            X ω lower T).mp ⟨t, hlt, hBad⟩
        obtain ⟨j, hj⟩ := hCover n hn k
        have hjT : τ j < T := by simpa only [hj] using hkT
        exact (hGrid j hjT) (by simpa only [hj] using hkBad)
      · have heq : t = T := le_antisymm ht (le_of_not_gt hlt)
        subst t
        exact hT hBad
  rw [hEvent]
  have hTerm : MeasurableSet[𝓕 T]
      {ω : Ω | ¬ X.X T ω < lower} := by
    exact (measurableSet_lt (X.adapted T) measurable_const).compl
  have hGrid : MeasurableSet[𝓕 T]
      (⋂ j : ℕ, {ω : Ω | τ j < T →
        ¬ X.X (τ j) ω < lower}) := by
    apply MeasurableSet.iInter
    intro j
    by_cases hj : τ j < T
    · have hXj : Measurable[𝓕 T] (X.X (τ j)) :=
        (X.adapted (τ j)).mono (𝓕.mono (le_of_lt hj)) le_rfl
      have hSafe : MeasurableSet[𝓕 T]
          {ω : Ω | lower ≤ X.X (τ j) ω} :=
        measurableSet_le measurable_const hXj
      simpa only [hj, true_implies, not_lt] using hSafe
    · simpa [hj] using
        (MeasurableSet.univ :
          MeasurableSet[𝓕 T] (Set.univ : Set Ω))
  exact hGrid.inter hTerm
