-- Prove2me | solution 2 for AvramDividend.Classical.bv_surviving_uniform_grid_deficit_caps
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-27T00:51:03.661702+00:00
-- url     : https://prove2.me/submissions/cf0b5afc-d287-47a6-9402-a23b23af627f

import Theorems.Thm_AvramDividend_Classical_zero_reflected_ruin_strict_survival_capital_monotone_prefix
import Definitions.Def_AvramDividend_Classical_ReflectionBarrier
import Mathlib.Tactic.Ring

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

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
  have hmono := zero_reflected_ruin_strict_survival_capital_monotone_prefix X ω T hBefore
    (ts k) (ts (k + 1)) (hOrder k hk) (hWithin k hk)
  have := hStepReal k hk
  have : X.drift * (ts (k + 1) : ℝ) - X.drift * (ts k : ℝ) = X.drift * (δ : ℝ) := by
    rw [← this]; ring
  linarith
