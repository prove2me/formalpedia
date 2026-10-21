-- Prove2me | solution 1 for AvramDividend.Classical.chat04_closed_horizon_survival_filtration_measurable
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-20T10:33:47.098738+00:00
-- url     : https://prove2.me/submissions/af8614c7-1507-47cc-8b28-c54ecb73a948

import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_chat04_closed_horizon_dense_survival_eq

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

/-!
Full pathwise survival through the closed horizon belongs to the filtration
at T, not merely the ambient Borel space. This permits conditioning on
survival at T in the genuine killed Markov process.
-/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (τ : ℕ → ℝ≥0)
    (hCover : ∀ n : ℕ, 0 < n → ∀ k : ℕ,
      ∃ j : ℕ, τ j = (k : ℝ≥0) * (n : ℝ≥0)⁻¹)
    (lower upper : ℝ) (T : ℝ≥0) :
    MeasurableSet[𝓕 T]
      {ω | ∀ t : ℝ≥0, t ≤ T →
        ¬ (X.X t ω < lower ∨ upper < X.X t ω)} := by
  rw [AvramDividend.Classical.chat04_closed_horizon_dense_survival_eq
    X τ hCover lower upper T]
  have hTermX : Measurable[𝓕 T] (X.X T) :=
    X.adapted T
  have hTermLow : MeasurableSet[𝓕 T]
      {ω : Ω | X.X T ω < lower} :=
    measurableSet_lt hTermX measurable_const
  have hTermUp : MeasurableSet[𝓕 T]
      {ω : Ω | upper < X.X T ω} :=
    measurableSet_lt measurable_const hTermX
  have hTerm : MeasurableSet[𝓕 T]
      {ω : Ω | ¬ (X.X T ω < lower ∨ upper < X.X T ω)} :=
    (hTermLow.union hTermUp).compl
  have hGrid : MeasurableSet[𝓕 T]
      (⋂ j : ℕ, {ω : Ω | τ j < T →
        ¬ (X.X (τ j) ω < lower ∨ upper < X.X (τ j) ω)}) := by
    apply MeasurableSet.iInter
    intro j
    by_cases hj : τ j < T
    · have hXj : Measurable[𝓕 T] (X.X (τ j)) :=
        (X.adapted (τ j)).mono (𝓕.mono (le_of_lt hj)) le_rfl
      have hLow : MeasurableSet[𝓕 T]
          {ω : Ω | X.X (τ j) ω < lower} :=
        measurableSet_lt hXj measurable_const
      have hUp : MeasurableSet[𝓕 T]
          {ω : Ω | upper < X.X (τ j) ω} :=
        measurableSet_lt measurable_const hXj
      have hNo : MeasurableSet[𝓕 T]
          {ω : Ω | ¬ (X.X (τ j) ω < lower ∨ upper < X.X (τ j) ω)} :=
        (hLow.union hUp).compl
      simpa [hj] using hNo
    · simpa [hj] using
        (MeasurableSet.univ :
          MeasurableSet[𝓕 T] (Set.univ : Set Ω))
  exact hGrid.inter hTerm
