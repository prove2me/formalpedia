-- Prove2me | solution 1 for AvramDividend.Classical.avram_jump6_A_original_finite_barrier_risk_strict_negative_at_physical_size2_first_mark
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-19T09:41:59.550213+00:00
-- url     : https://prove2.me/submissions/cfa6638e-626a-40ad-98a7-0209094ca4ad

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
    (hTube : ∀ t : ℝ≥0, t ≤ σ → |B t| < (1 / 4000 : ℝ))
    (hMark : 1 ≤ N σ) :
    riskProcess X (1 / 10 : ℝ)
      (barrierStrategy X (1 / 10 : ℝ) (1 / 5 : ℝ)) σ ω < 0 := by
  have hPay :
      barrierStrategy X (1 / 10 : ℝ) (1 / 5 : ℝ) σ ω = 0 := by
    apply barrierStrategy_zero_before_upcrossing
    intro s hs
    rw [hPath s]
    have hb : B s < (1 / 4000 : ℝ) :=
      (abs_lt.mp (hTube s hs)).2
    have hn : (0 : ℝ) ≤ (N s : ℝ) := Nat.cast_nonneg _
    nlinarith
  change (1 / 10 : ℝ) + X.X σ ω -
    barrierStrategy X (1 / 10 : ℝ) (1 / 5 : ℝ) σ ω < 0
  rw [hPay, hPath σ]
  have hb : B σ < (1 / 4000 : ℝ) :=
    (abs_lt.mp (hTube σ le_rfl)).2
  have hn : (1 : ℝ) ≤ (N σ : ℝ) := by exact_mod_cast hMark
  nlinarith
