-- Prove2me | solution 1 for AvramDividend.Classical.avram_jump6_A_original_Brownian_size2_Poisson_short_tube_barrier_pays_zero
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-19T09:36:35.204208+00:00
-- url     : https://prove2.me/submissions/a353fa6b-73ad-4736-b80c-500f4bda8642

import Mathlib
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_barrierStrategy_zero_before_upcrossing
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

set_option autoImplicit false
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section
theorem solution
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 ‹MeasurableSpace Ω›}
    (X : SpectrallyNegativeLevy P 𝓕)
    (ω : Ω) (B : ℝ≥0 → ℝ) (N : ℝ≥0 → ℕ)
    (σ : ℝ≥0)
    (hPath : ∀ t : ℝ≥0, X.X t ω = B t - 2 * (N t : ℝ))
    (hTube : ∀ t : ℝ≥0, t ≤ σ → |B t| < (1 / 4000 : ℝ)) :
    ∀ t : ℝ≥0, t ≤ σ →
      barrierStrategy X (1 / 10 : ℝ) (1 / 5 : ℝ) t ω = 0 := by
  intro t ht
  apply barrierStrategy_zero_before_upcrossing X (1 / 10 : ℝ) (1 / 5 : ℝ) t ω
  intro s hs
  rw [hPath s]
  have hB : B s < (1 / 4000 : ℝ) :=
    (abs_lt.mp (hTube s (le_trans hs ht))).2
  have hN : (0 : ℝ) ≤ (N s : ℝ) := Nat.cast_nonneg _
  nlinarith
