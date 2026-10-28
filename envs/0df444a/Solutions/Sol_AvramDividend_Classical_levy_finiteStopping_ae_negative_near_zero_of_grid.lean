-- Prove2me | solution 1 for AvramDividend.Classical.levy_finiteStopping_ae_negative_near_zero_of_grid
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-26T11:41:57.733419+00:00
-- url     : https://prove2.me/submissions/0d196de6-815c-484f-8308-3c38d5e92652

import Mathlib.Probability.Process.Stopping
import Theorems.Thm_AvramDividend_Classical_levy_finiteStopping_ae_negative_grid_transfer
import Theorems.Thm_AvramDividend_Classical_ae_negative_near_zero_of_ae_countable_grid

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (τ : Ω → ℝ≥0)
    (hτ : ∀ s : ℝ≥0, MeasurableSet[𝓕 s] {ω : Ω | τ ω ≤ s})
    (hstop : IsStoppingTime 𝓕 (fun ω => (τ ω : WithTop ℝ≥0)))
    (hOrigMeas : Measurable (fun ω : Ω => fun t : ℝ≥0 => X.X t ω))
    (times horizons : ℕ → ℝ≥0)
    (hcofinal : ∀ ε : ℝ≥0, 0 < ε → ∃ n : ℕ, horizons n ≤ ε)
    (hGridAE : ∀ᵐ ω ∂P, ∀ n : ℕ, ∃ m : ℕ,
      times m < horizons n ∧ X.X (times m) ω < 0) :
    ∀ᵐ ω ∂P, ∀ ε : ℝ≥0, 0 < ε →
      ∃ s : ℝ≥0, s < ε ∧
        X.X (τ ω + s) ω - X.X (τ ω) ω < 0 := by
  have hShiftGrid :=
    levy_finiteStopping_ae_negative_grid_transfer
      X τ hτ hstop hOrigMeas times horizons hGridAE
  refine hShiftGrid.mono ?_
  intro ω hω ε hε
  obtain ⟨n, hn⟩ := hcofinal ε hε
  obtain ⟨m, hm, hneg⟩ := hω n
  exact ⟨times m, lt_of_lt_of_le hm hn, hneg⟩
