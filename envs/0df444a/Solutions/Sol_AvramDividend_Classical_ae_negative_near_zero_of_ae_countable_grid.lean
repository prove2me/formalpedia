-- Prove2me | solution 1 for AvramDividend.Classical.ae_negative_near_zero_of_ae_countable_grid
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-26T11:16:12.041232+00:00
-- url     : https://prove2.me/submissions/a3c0e76f-9323-4e04-b012-eaaf57347edd

import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Mathlib.Data.NNReal.Defs
import Mathlib.MeasureTheory.MeasurableSpace.Defs

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (times horizons : ℕ → ℝ≥0)
    (hcofinal : ∀ ε : ℝ≥0, 0 < ε → ∃ n : ℕ, horizons n ≤ ε)
    (hGridAE : ∀ᵐ ω ∂P, ∀ n : ℕ, ∃ m : ℕ,
      times m < horizons n ∧ X.X (times m) ω < 0) :
    ∀ᵐ ω ∂P, ∀ ε : ℝ≥0, 0 < ε →
      ∃ s : ℝ≥0, s < ε ∧ X.X s ω < 0 := by
  refine hGridAE.mono ?_
  intro ω hω ε hε
  obtain ⟨n, hn⟩ := hcofinal ε hε
  obtain ⟨m, hm, hneg⟩ := hω n
  exact ⟨times m, lt_of_lt_of_le hm hn, hneg⟩
