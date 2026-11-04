-- Prove2me | solution 1 for AvramDividend.Classical.avram_p3_b_bvjump_original_stopped_clock_support_from_tau_bound
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T12:47:52.235679+00:00
-- url     : https://prove2.me/submissions/85d88b6b-1cad-4296-a30c-49182d872a2f

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- An actual horizon-bounded stopping time forces the stopped kernel to vanish after T. -/
theorem solution
    {Ω : Type*} (T : ℝ≥0) (τ : Ω → ℝ≥0)
    (hτBound : ∀ ω, τ ω ≤ T)
    (G H : ((ℝ≥0 × Ω) × ℝ) → ℝ)
    (hH : H = fun p =>
      if (p.1.1 : ℝ≥0∞) ≤ (τ p.1.2 : ℝ≥0∞) then G p else 0) :
    ({p : ((ℝ≥0 × Ω) × ℝ) | p.1.1 ≤ T} : Set _).indicator H = H := by
  funext p
  by_cases hp : p.1.1 ≤ T
  · simp [Set.indicator, hp]
  · have hnotNN : ¬ p.1.1 ≤ τ p.1.2 := by
      intro hle
      exact hp (hle.trans (hτBound p.1.2))
    simp [Set.indicator, hp, hH, hnotNN]
