-- Prove2me | solution 1 for AvramDividend.Classical.chat04_closed_horizon_survival_lintegral_grid_limit
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-20T21:41:09.238106+00:00
-- url     : https://prove2.me/submissions/07336102-958e-484a-950b-c7ef174e1f54

import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_chat04_closed_horizon_dense_survival_eq
import Theorems.Thm_AvramDividend_Classical_chat04_countable_grid_survival_prefix_limit

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

/-!
A payoff killed on the CLOSED continuous horizon [0,T] is the decreasing
limit of finite-grid expectations with a mandatory terminal-time observation.
No zero-probability jump-at-T assumption is made.
-/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (τ : ℕ → ℝ≥0)
    (hCover : ∀ n : ℕ, 0 < n → ∀ k : ℕ,
      ∃ j : ℕ, τ j = (k : ℝ≥0) * (n : ℝ≥0)⁻¹)
    (lower upper : ℝ) (T : ℝ≥0)
    (g : Ω → ℝ≥0∞) (hg : Measurable g)
    (hFin : (∫⁻ ω, g ω ∂P) ≠ ∞) :
    (∫⁻ ω,
      ({ω | ∀ t : ℝ≥0, t ≤ T →
        ¬ (X.X t ω < lower ∨ upper < X.X t ω)}).indicator g ω ∂P) =
      ⨅ n : ℕ, ∫⁻ ω,
        ({ω | ∀ j ≤ n,
          (τ j < T →
            ¬ (X.X (τ j) ω < lower ∨ upper < X.X (τ j) ω)) ∧
          ¬ (X.X T ω < lower ∨ upper < X.X T ω)}).indicator g ω ∂P := by
  let B : ℕ → Set Ω := fun j =>
    {ω | (τ j < T →
      ¬ (X.X (τ j) ω < lower ∨ upper < X.X (τ j) ω)) ∧
      ¬ (X.X T ω < lower ∨ upper < X.X T ω)}
  have hTMeas : Measurable (X.X T) :=
    (X.adapted T).mono (𝓕.le T) le_rfl
  have hTermLow :
      MeasurableSet {ω : Ω | X.X T ω < lower} :=
    measurableSet_lt hTMeas measurable_const
  have hTermHigh :
      MeasurableSet {ω : Ω | upper < X.X T ω} :=
    measurableSet_lt measurable_const hTMeas
  have hTerminal :
      MeasurableSet {ω : Ω |
        ¬ (X.X T ω < lower ∨ upper < X.X T ω)} :=
    (hTermLow.union hTermHigh).compl
  have hB : ∀ j, MeasurableSet (B j) := by
    intro j
    have hXt : Measurable (X.X (τ j)) :=
      (X.adapted (τ j)).mono (𝓕.le (τ j)) le_rfl
    have hLow :
        MeasurableSet {ω : Ω | X.X (τ j) ω < lower} :=
      measurableSet_lt hXt measurable_const
    have hHigh :
        MeasurableSet {ω : Ω | upper < X.X (τ j) ω} :=
      measurableSet_lt measurable_const hXt
    have hNoExit :
        MeasurableSet {ω : Ω |
          ¬ (X.X (τ j) ω < lower ∨ upper < X.X (τ j) ω)} :=
      (hLow.union hHigh).compl
    have hGuard :
        MeasurableSet {ω : Ω | τ j < T →
          ¬ (X.X (τ j) ω < lower ∨ upper < X.X (τ j) ω)} := by
      by_cases hj : τ j < T
      · simpa [hj] using hNoExit
      · simpa [hj] using
          (MeasurableSet.univ : MeasurableSet (Set.univ : Set Ω))
    change MeasurableSet
      ({ω : Ω | τ j < T →
        ¬ (X.X (τ j) ω < lower ∨ upper < X.X (τ j) ω)} ∩
       {ω : Ω | ¬ (X.X T ω < lower ∨ upper < X.X T ω)})
    exact hGuard.inter hTerminal
  have hEvent :
      {ω | ∀ t : ℝ≥0, t ≤ T →
        ¬ (X.X t ω < lower ∨ upper < X.X t ω)} =
      ⋂ j, B j := by
    rw [AvramDividend.Classical.chat04_closed_horizon_dense_survival_eq
      X τ hCover lower upper T]
    ext ω
    simp only [Set.mem_inter_iff, Set.mem_iInter, Set.mem_setOf_eq, B]
    constructor
    · rintro ⟨hGrid, hTerm⟩ j
      exact ⟨hGrid j, hTerm⟩
    · intro h
      constructor
      · intro j
        exact (h j).1
      · exact (h 0).2
  rw [hEvent]
  simpa only [B, Set.mem_setOf_eq] using
    (AvramDividend.Classical.chat04_countable_grid_survival_prefix_limit
      B hB g hg hFin)
