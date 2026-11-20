-- Prove2me | solution 1 for AvramDividend.Classical.avram_jump6_A_original_early_firstsize2_mark_all_precounts_zero_positive_event
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-19T12:52:39.084741+00:00
-- url     : https://prove2.me/submissions/6315bf1d-3e0d-471f-85bc-9734a6f6d7a0

import Mathlib
import Definitions.Def_LeanLevy_Processes_CompoundPoisson
import Definitions.Def_LeanLevy_Processes_PiecewisePath
import Theorems.Thm_AvramDividend_Classical_avram_jump6_A_actual_first_mark_count_zero_before_and_one_at_arrival_ae
import Theorems.Thm_AvramDividend_Classical_avram_jump6_A_original_rateone_size2_first_mark_strictly_positive_and_early_event
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

set_option autoImplicit false
open MeasureTheory ProbabilityTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section
theorem solution
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (τ Y : ℕ → Ω → ℝ)
    (hJ : IsCompoundPoissonDriver τ Y (1 : ℝ≥0)
      (Measure.dirac (-2 : ℝ)) μ) :
    0 < μ (
      {ω : Ω |
        (∀ t : ℝ≥0, (t : ℝ) < arrival τ 0 ω →
          jumpCount (fun n => arrival τ n ω) (t : ℝ) = 0) ∧
        jumpCount (fun n => arrival τ n ω) (arrival τ 0 ω) = 1} ∩
      {ω : Ω | 0 < τ 0 ω ∧ τ 0 ω ≤ (1 / 500 : ℝ)}) := by
  have hEarly : 0 < μ {ω : Ω |
      0 < τ 0 ω ∧ τ 0 ω ≤ (1 / 500 : ℝ)} :=
    avram_jump6_A_original_rateone_size2_first_mark_strictly_positive_and_early_event
      μ τ Y hJ
  have hCount : ∀ᵐ ω ∂μ,
      (∀ t : ℝ≥0, (t : ℝ) < arrival τ 0 ω →
        jumpCount (fun n => arrival τ n ω) (t : ℝ) = 0) ∧
      jumpCount (fun n => arrival τ n ω) (arrival τ 0 ω) = 1 :=
    avram_jump6_A_actual_first_mark_count_zero_before_and_one_at_arrival_ae
      μ τ Y hJ
  have hEq : μ (
      {ω : Ω |
        (∀ t : ℝ≥0, (t : ℝ) < arrival τ 0 ω →
          jumpCount (fun n => arrival τ n ω) (t : ℝ) = 0) ∧
        jumpCount (fun n => arrival τ n ω) (arrival τ 0 ω) = 1} ∩
      {ω : Ω | 0 < τ 0 ω ∧ τ 0 ω ≤ (1 / 500 : ℝ)}) =
      μ {ω : Ω | 0 < τ 0 ω ∧ τ 0 ω ≤ (1 / 500 : ℝ)} :=
    Measure.measure_inter_eq_of_ae hCount
  rw [hEq]
  exact hEarly
