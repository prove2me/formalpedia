-- Prove2me | solution 1 for AvramDividend.Classical.bv_surviving_uniform_grid_deficit_caps
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-27T00:49:58.215494+00:00
-- url     : https://prove2.me/submissions/bfa394a6-ff0d-4e43-ad85-261e7a85d163

import Theorems.Thm_AvramDividend_Classical_zero_reflected_ruin_strict_survival_capital_monotone_prefix
import Definitions.Def_AvramDividend_Classical_ReflectionBarrier
import Mathlib.Tactic.Ring
import Mathlib.MeasureTheory.MeasurableSpace.Defs

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

/-- Before strict zero-barrier ruin, every mesh drift-deficit increment is drift-capped. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (T : ℝ≥0) (N : ℕ) (ts : ℕ → ℝ≥0) (δ : ℝ≥0)
    (hOrder : ∀ k : ℕ, k < N → ts k ≤ ts (k + 1))
    (hWithin : ∀ k : ℕ, k < N → ts (k + 1) ≤ T)
    (hStepReal : ∀ k : ℕ, k < N →
      (ts (k + 1) : ℝ) - (ts k : ℝ) = (δ : ℝ))
    (ω : Ω)
    (hBefore : (T : ℝ≥0∞) < barrierRuinTime X 0 ω) :
    ∀ k : ℕ, k < N →
      (X.drift * (ts (k + 1) : ℝ) - X.X (ts (k + 1)) ω) -
        (X.drift * (ts k : ℝ) - X.X (ts k) ω) ≤
      X.drift * (δ : ℝ) := by
  intro k hk
  have hCapital :=
    zero_reflected_ruin_strict_survival_capital_monotone_prefix
      X ω T hBefore
        (ts k) (ts (k + 1)) (hOrder k hk) (hWithin k hk)
  calc
    (X.drift * (ts (k + 1) : ℝ) - X.X (ts (k + 1)) ω) -
        (X.drift * (ts k : ℝ) - X.X (ts k) ω) =
      X.drift * ((ts (k + 1) : ℝ) - (ts k : ℝ)) -
        (X.X (ts (k + 1)) ω - X.X (ts k) ω) := by ring
    _ ≤ X.drift * ((ts (k + 1) : ℝ) - (ts k : ℝ)) :=
      sub_le_self _ (sub_nonneg.mpr hCapital)
    _ = X.drift * (δ : ℝ) := by rw [hStepReal k hk]
