-- Prove2me | solution 1 for AvramDividend.Classical.avram_jump6_A_original_rateone_size2_first_mark_strictly_positive_and_early_event
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-19T12:46:49.46746+00:00
-- url     : https://prove2.me/submissions/0cd70d9a-75f5-456f-9c55-048d9bc357ce

import Mathlib
import Definitions.Def_LeanLevy_Processes_CompoundPoisson
import Theorems.Thm_ProbabilityTheory_IsCompoundPoissonDriver_ae_interarrival_pos
import Theorems.Thm_AvramDividend_Classical_avram_jump6_A_actual_first_size2_mark_positive_before_any_time
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
    0 < μ {ω : Ω | 0 < τ 0 ω ∧ τ 0 ω ≤ (1 / 500 : ℝ)} := by
  have hEarly : 0 < μ {ω : Ω | τ 0 ω ≤ (1 / 500 : ℝ)} :=
    avram_jump6_A_actual_first_size2_mark_positive_before_any_time
      μ τ Y hJ (1 / 500 : ℝ) (by norm_num)
  have hPos : ∀ᵐ ω ∂μ, 0 < τ 0 ω := by
    filter_upwards [IsCompoundPoissonDriver.ae_interarrival_pos
      hJ (by norm_num)] with ω hω
    exact hω 0
  change 0 < μ ({ω : Ω | 0 < τ 0 ω} ∩
    {ω : Ω | τ 0 ω ≤ (1 / 500 : ℝ)})
  have hEq : μ ({ω : Ω | 0 < τ 0 ω} ∩
      {ω : Ω | τ 0 ω ≤ (1 / 500 : ℝ)}) =
      μ {ω : Ω | τ 0 ω ≤ (1 / 500 : ℝ)} :=
    Measure.measure_inter_eq_of_ae hPos
  simpa only [hEq] using hEarly
