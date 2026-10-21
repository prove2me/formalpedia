-- Prove2me | solution 1 for AvramDividend.Classical.chat04_continuous_survival_payoff_lintegral_grid_limit
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-20T09:57:34.266051+00:00
-- url     : https://prove2.me/submissions/c3fdd928-abf0-40f4-ba2e-4f6bf0670a82

import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_chat04_countable_grid_strict_survival_event_eq
import Theorems.Thm_AvramDividend_Classical_chat04_countable_grid_survival_prefix_limit
import Mathlib.MeasureTheory.MeasurableSpace.Defs

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

/-!
A finite-mass terminal payoff killed by *continuous-time* strict exit is
the decreasing limit of the expected finite-grid survival payoffs. Covers
both sides and every sample path by càdlàg strict-event density.
-/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (τ : ℕ → ℝ≥0)
    (hCover : ∀ n : ℕ, 0 < n → ∀ k : ℕ,
      ∃ j : ℕ, τ j = (k : ℝ≥0) * (n : ℝ≥0)⁻¹)
    (lower upper : ℝ)
    (g : Ω → ℝ≥0∞) (hg : Measurable g)
    (hFin : (∫⁻ ω, g ω ∂P) ≠ ∞) :
    (∫⁻ ω,
      ({ω | ∀ t : ℝ≥0,
        ¬ (X.X t ω < lower ∨ upper < X.X t ω)}).indicator g ω ∂P) =
      ⨅ n : ℕ, ∫⁻ ω,
        ({ω | ∀ k ≤ n,
          ¬ (X.X (τ k) ω < lower ∨ upper < X.X (τ k) ω)}).indicator g ω ∂P := by
  let B : ℕ → Set Ω := fun k =>
    {ω | ¬ (X.X (τ k) ω < lower ∨ upper < X.X (τ k) ω)}
  have hB : ∀ k, MeasurableSet (B k) := by
    intro k
    have hXt : Measurable (X.X (τ k)) :=
      (X.adapted (τ k)).mono (𝓕.le (τ k)) le_rfl
    have hLow : MeasurableSet {ω : Ω | X.X (τ k) ω < lower} :=
      measurableSet_lt hXt measurable_const
    have hUp : MeasurableSet {ω : Ω | upper < X.X (τ k) ω} :=
      measurableSet_lt measurable_const hXt
    change MeasurableSet
      ({ω : Ω | X.X (τ k) ω < lower ∨ upper < X.X (τ k) ω}ᶜ)
    exact (hLow.union hUp).compl
  have hEvents :
      {ω | ∀ t : ℝ≥0,
        ¬ (X.X t ω < lower ∨ upper < X.X t ω)} =
      ⋂ k, B k := by
    simpa only [B] using
      AvramDividend.Classical.chat04_countable_grid_strict_survival_event_eq
        X τ hCover lower upper
  rw [hEvents]
  simpa only [B, Set.mem_setOf_eq] using
    (AvramDividend.Classical.chat04_countable_grid_survival_prefix_limit
      B hB g hg hFin)
