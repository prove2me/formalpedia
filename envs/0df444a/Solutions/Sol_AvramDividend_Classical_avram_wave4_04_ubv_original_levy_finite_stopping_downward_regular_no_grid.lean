-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave4_04_ubv_original_levy_finite_stopping_downward_regular_no_grid
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-31T16:27:48.203147+00:00
-- url     : https://prove2.me/submissions/f0d251bb-6eb5-46b7-b35b-b13c2fe47410

import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Mathlib.Tactic.Positivity
import Mathlib.Topology.Order.OrderClosed
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_ae_negative_near_zero_of_unbounded_variation
import Theorems.Thm_AvramDividend_Classical_levy_negative_before_horizon_iff_dense_grid
import Theorems.Thm_AvramDividend_Classical_levy_finiteStopping_negative_near_zero_of_grid

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal

/-!
Every finite stopping time has immediate negative original Lévy increments
almost surely in the unbounded-variation branch. All countable schedules
needed by the canonical same-filtration strong Markov grid result are
constructed here, so no exogenous grid is imposed on callers.
-/

private theorem denseCofinalSchedules :
    ∃ (times horizons : ℕ → ℝ≥0),
      (∀ a b : ℝ≥0, a < b →
        ∃ m : ℕ, a < times m ∧ times m < b) ∧
      (∀ n : ℕ, 0 < horizons n) ∧
      (∀ ε : ℝ≥0, 0 < ε →
        ∃ n : ℕ, horizons n ≤ ε) := by
  obtain ⟨times, hDense⟩ :=
    TopologicalSpace.exists_dense_seq ℝ≥0
  let horizons : ℕ → ℝ≥0 := fun n => 1 / ((n : ℝ≥0) + 1)
  refine ⟨times, horizons, ?_, ?_, ?_⟩
  · intro a b hab
    obtain ⟨z, ⟨n, hn⟩, hz⟩ := Dense.exists_between hDense hab
    refine ⟨n, ?_, ?_⟩
    · simpa only [← hn] using hz.1
    · simpa only [← hn] using hz.2
  · intro n
    dsimp [horizons]
    positivity
  · intro ε hε
    obtain ⟨n, hn⟩ := exists_nat_one_div_lt hε
    exact ⟨n, le_of_lt hn⟩

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hBV : ¬ X.BoundedVariation)
    (τ : Ω → ℝ≥0)
    (hτ : ∀ s : ℝ≥0,
      MeasurableSet[𝓕 s] {ω : Ω | τ ω ≤ s})
    (hstop : IsStoppingTime 𝓕 (fun ω => (τ ω : WithTop ℝ≥0))) :
    ∀ᵐ ω ∂P, ∀ ε : ℝ≥0, 0 < ε →
      ∃ s : ℝ≥0, s < ε ∧
        X.X (τ ω + s) ω - X.X (τ ω) ω < 0 := by
  obtain ⟨times, horizons, hdense, hpos, hcofinal⟩ :=
    denseCofinalSchedules
  have hRegular := ae_negative_near_zero_of_unbounded_variation X hBV
  have hGridAE : ∀ᵐ ω ∂P, ∀ n : ℕ, ∃ m : ℕ,
      times m < horizons n ∧ X.X (times m) ω < 0 := by
    filter_upwards [hRegular] with ω hω
    intro n
    exact (levy_negative_before_horizon_iff_dense_grid
      X times hdense ω (horizons n)).1
      (hω (horizons n) (hpos n))
  exact levy_finiteStopping_negative_near_zero_of_grid
    X τ hτ hstop times horizons hcofinal hGridAE
