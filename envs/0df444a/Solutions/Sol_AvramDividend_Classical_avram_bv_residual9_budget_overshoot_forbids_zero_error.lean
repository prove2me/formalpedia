-- Prove2me | solution 1 for AvramDividend.Classical.avram_bv_residual9_budget_overshoot_forbids_zero_error
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-07T09:55:57.850178+00:00
-- url     : https://prove2.me/submissions/b438b3e4-d6fa-40e5-b2dd-26867f740dba

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_bv_residual9_budget_expected_error_lower_bound
import Theorems.Thm_AvramDividend_Classical_avram_bv_residual9_positive_error_lower_bound_blocks_zero_limit
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Classical MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P]
    (a ε : ℝ) (hε : 0 < ε)
    (F M B E : ℕ → Ω → ℝ)
    (hF : ∀ n, Integrable (F n) P ∧ ∀ᵐ ω ∂P, 0 ≤ F n ω)
    (hM : ∀ n, Integrable (M n) P ∧ (∫ ω, M n ω ∂P) = 0)
    (hB : ∀ n, Integrable (B n) P)
    (hE : ∀ n, Integrable (E n) P)
    (hBneg : ∀ n, (∫ ω, B n ω ∂P) ≤ -a - ε)
    (hbudget : ∀ n, ∀ᵐ ω ∂P,
      F n ω ≤ a + M n ω + B n ω + E n ω) :
    ¬ Tendsto (fun n => ∫ ω, E n ω ∂P)
      atTop (nhds (0 : ℝ)) := by
  have hfloor : ∀ n, ε ≤ ∫ ω, E n ω ∂P :=
    avram_bv_residual9_budget_expected_error_lower_bound
      a ε hε F M B E hF hM hB hE hBneg hbudget
  exact avram_bv_residual9_positive_error_lower_bound_blocks_zero_limit
    ε hε _ hfloor
