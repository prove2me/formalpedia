-- Prove2me | solution 1 for AvramDividend.Classical.avram_bv_residual9_negative_budget_excludes_vanishing_positive_error
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-07T17:31:56.559466+00:00
-- url     : https://prove2.me/submissions/5d2ab33a-44f7-47ce-bdc5-0dc5adae5fc6

import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Theorems.Thm_AvramDividend_Classical_avram_bv_residual9_budget_positive_error_expected_floor
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter AvramDividend.Classical
noncomputable section

/-- A uniformly negative mean budget cannot admit an L1-vanishing
positive-error certificate with nonnegative payoff and centred noise. -/
theorem solution
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P]
    (c ε : ℝ) (hε : 0 < ε) (F M B Err : ℕ → Ω → ℝ)
    (hF : ∀ n, ∀ᵐ ω ∂P, 0 ≤ F n ω)
    (hM : ∀ n, Integrable (M n) P)
    (hM0 : ∀ n, (∫ ω, M n ω ∂P) = 0)
    (hB : ∀ n, Integrable (B n) P)
    (hErr : ∀ n, Integrable (fun ω => max (Err n ω) 0) P)
    (hBudget : ∀ n, ∀ᵐ ω ∂P,
      F n ω ≤ c + M n ω + B n ω + max (Err n ω) 0)
    (hNeg : ∀ n, (∫ ω, B n ω ∂P) ≤ -c - ε) :
    ¬ Tendsto (fun n => ∫ ω, max (Err n ω) 0 ∂P) atTop (nhds (0 : ℝ)) := by
  intro hT
  have hLower (n : ℕ) :
      ε ≤ (∫ ω, max (Err n ω) 0 ∂P) := by
    have hFloor := avram_bv_residual9_budget_positive_error_expected_floor
      c (F n) (M n) (B n) (Err n)
      (hF n) (hM n) (hM0 n) (hB n) (hErr n) (hBudget n)
    linarith [hNeg n]
  have hZero : (0 : ℝ) ≥ ε :=
    ge_of_tendsto hT (Filter.Eventually.of_forall hLower)
  linarith
