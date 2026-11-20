-- Prove2me | solution 1 for AvramDividend.Classical.avram_jump6_A_actual_Brownian_negative_mark_tube_forces_ruin_without_upper_cap_exit
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-19T08:57:22.434377+00:00
-- url     : https://prove2.me/submissions/5dd84a8e-14bc-4937-8a92-65590ca902ed

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

set_option autoImplicit false
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section
theorem solution
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 ‹MeasurableSpace Ω›}
    (X : SpectrallyNegativeLevy P 𝓕)
    (ω : Ω) (B : ℝ≥0 → ℝ) (N : ℝ≥0 → ℕ)
    (σ : ℝ≥0)
    (hOriginal : ∀ t : ℝ≥0, X.X t ω = B t - 2 * (N t : ℝ))
    (hTube : ∀ t : ℝ≥0, t ≤ σ → |B t| < (1 / 4000 : ℝ))
    (hMark : 1 ≤ N σ) :
    (∀ t : ℝ≥0, t ≤ σ → X.X t ω ≤ (1 / 10 : ℝ)) ∧
    (1 / 10 : ℝ) + X.X σ ω < 0 := by
  constructor
  · intro t ht
    rw [hOriginal t]
    have hBup : B t < (1 / 4000 : ℝ) := (abs_lt.mp (hTube t ht)).2
    have hNnonneg : (0 : ℝ) ≤ (N t : ℝ) := Nat.cast_nonneg _
    nlinarith
  · rw [hOriginal σ]
    have hBup : B σ < (1 / 4000 : ℝ) :=
      (abs_lt.mp (hTube σ le_rfl)).2
    have hNmark : (1 : ℝ) ≤ (N σ : ℝ) := by exact_mod_cast hMark
    nlinarith
