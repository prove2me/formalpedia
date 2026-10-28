-- Prove2me | solution 1 for AvramDividend.Classical.levy_negative_near_zero_preserved_by_local_absoluteContinuity
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-26T13:59:46.971562+00:00
-- url     : https://prove2.me/submissions/2b480d8e-c0b0-44d9-8d08-bb6cf7e550c6

import Theorems.Thm_AvramDividend_Classical_levy_measurableSet_early_negative_before_horizon
import Theorems.Thm_AvramDividend_Classical_ae_negative_near_zero_of_local_absoluteContinuity
import Mathlib.MeasureTheory.MeasurableSpace.Defs

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P Q : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (times horizons : ℕ → ℝ≥0)
    (hdense : ∀ a b : ℝ≥0, a < b →
      ∃ m : ℕ, a < times m ∧ times m < b)
    (hpos : ∀ n : ℕ, 0 < horizons n)
    (hcofinal : ∀ ε : ℝ≥0, 0 < ε →
      ∃ n : ℕ, horizons n ≤ ε)
    (hLocalAC : ∀ n : ℕ, ∀ A : Set Ω,
      MeasurableSet[𝓕 (horizons n)] A →
        P A = 0 → Q A = 0)
    (hRegP : ∀ᵐ ω ∂P, ∀ ε : ℝ≥0, 0 < ε →
      ∃ t : ℝ≥0, t < ε ∧ X.X t ω < 0) :
    ∀ᵐ ω ∂Q, ∀ ε : ℝ≥0, 0 < ε →
      ∃ t : ℝ≥0, t < ε ∧ X.X t ω < 0 := by
  exact ae_negative_near_zero_of_local_absoluteContinuity
    P Q X.X horizons hpos hcofinal
    (fun n =>
      levy_measurableSet_early_negative_before_horizon
        X times hdense (horizons n))
    hLocalAC hRegP
