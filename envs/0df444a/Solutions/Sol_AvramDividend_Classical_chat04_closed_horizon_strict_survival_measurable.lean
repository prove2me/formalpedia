-- Prove2me | solution 1 for AvramDividend.Classical.chat04_closed_horizon_strict_survival_measurable
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-20T10:28:30.527124+00:00
-- url     : https://prove2.me/submissions/4649c2f5-76f0-4799-8d41-9c2d5978b889

import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_chat04_closed_horizon_dense_survival_eq
import Mathlib.MeasureTheory.MeasurableSpace.Defs

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

/-!
The full finite-horizon survival event is measurable although its original
definition quantifies over uncountably many times. The accepted dense-grid
representation reduces it to countably many Borel observations, including T.
-/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (τ : ℕ → ℝ≥0)
    (hCover : ∀ n : ℕ, 0 < n → ∀ k : ℕ,
      ∃ j : ℕ, τ j = (k : ℝ≥0) * (n : ℝ≥0)⁻¹)
    (lower upper : ℝ) (T : ℝ≥0) :
    MeasurableSet
      {ω | ∀ t : ℝ≥0, t ≤ T →
        ¬ (X.X t ω < lower ∨ upper < X.X t ω)} := by
  rw [AvramDividend.Classical.chat04_closed_horizon_dense_survival_eq
    X τ hCover lower upper T]
  have hXt : Measurable (X.X T) :=
    (X.adapted T).mono (𝓕.le T) le_rfl
  have hLowT : MeasurableSet {ω : Ω | X.X T ω < lower} :=
    measurableSet_lt hXt measurable_const
  have hUpT : MeasurableSet {ω : Ω | upper < X.X T ω} :=
    measurableSet_lt measurable_const hXt
  have hTerm : MeasurableSet
      {ω : Ω | ¬ (X.X T ω < lower ∨ upper < X.X T ω)} :=
    (hLowT.union hUpT).compl
  have hGrid : MeasurableSet
      (⋂ j : ℕ, {ω : Ω | τ j < T →
        ¬ (X.X (τ j) ω < lower ∨ upper < X.X (τ j) ω)}) := by
    apply MeasurableSet.iInter
    intro j
    have hXm : Measurable (X.X (τ j)) :=
      (X.adapted (τ j)).mono (𝓕.le (τ j)) le_rfl
    have hLow : MeasurableSet
        {ω : Ω | X.X (τ j) ω < lower} :=
      measurableSet_lt hXm measurable_const
    have hUp : MeasurableSet
        {ω : Ω | upper < X.X (τ j) ω} :=
      measurableSet_lt measurable_const hXm
    have hNo : MeasurableSet
        {ω : Ω | ¬ (X.X (τ j) ω < lower ∨ upper < X.X (τ j) ω)} :=
      (hLow.union hUp).compl
    by_cases hlt : τ j < T
    · simpa [hlt] using hNo
    · simpa [hlt] using
        (MeasurableSet.univ : MeasurableSet (Set.univ : Set Ω))
  exact hGrid.inter hTerm
