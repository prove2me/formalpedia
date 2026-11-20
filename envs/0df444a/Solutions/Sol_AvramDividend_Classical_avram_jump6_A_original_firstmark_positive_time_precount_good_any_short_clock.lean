-- Prove2me | solution 1 for AvramDividend.Classical.avram_jump6_A_original_firstmark_positive_time_precount_good_any_short_clock
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-19T12:55:16.312771+00:00
-- url     : https://prove2.me/submissions/1d227285-5ab9-47fc-8438-6b18e2b82096

import Mathlib
import Definitions.Def_LeanLevy_Processes_CompoundPoisson
import Definitions.Def_LeanLevy_Processes_PiecewisePath
import Theorems.Thm_ProbabilityTheory_IsCompoundPoissonDriver_ae_interarrival_pos
import Theorems.Thm_AvramDividend_Classical_avram_jump6_A_actual_first_size2_mark_positive_before_any_time
import Theorems.Thm_AvramDividend_Classical_avram_jump6_A_actual_first_mark_count_zero_before_and_one_at_arrival_ae
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
      (Measure.dirac (-2 : ℝ)) μ)
    (horizon : ℝ) (hh : 0 < horizon) :
    0 < μ (
      {j : Ω |
        0 < τ 0 j ∧
        (∀ s : ℝ≥0, (s : ℝ) < arrival τ 0 j →
          jumpCount (fun n => arrival τ n j) (s : ℝ) = 0) ∧
        jumpCount (fun n => arrival τ n j) (arrival τ 0 j) = 1} ∩
      {j : Ω | τ 0 j ≤ horizon}) := by
  have hEarly : 0 < μ {j : Ω | τ 0 j ≤ horizon} :=
    avram_jump6_A_actual_first_size2_mark_positive_before_any_time
      μ τ Y hJ horizon hh
  have hCount : ∀ᵐ j ∂μ,
      (∀ s : ℝ≥0, (s : ℝ) < arrival τ 0 j →
        jumpCount (fun n => arrival τ n j) (s : ℝ) = 0) ∧
      jumpCount (fun n => arrival τ n j) (arrival τ 0 j) = 1 :=
    avram_jump6_A_actual_first_mark_count_zero_before_and_one_at_arrival_ae
      μ τ Y hJ
  have hPos : ∀ᵐ j ∂μ, 0 < τ 0 j := by
    filter_upwards [IsCompoundPoissonDriver.ae_interarrival_pos
      hJ (by norm_num)] with j hj
    exact hj 0
  have hGood : ∀ᵐ j ∂μ,
      0 < τ 0 j ∧
      (∀ s : ℝ≥0, (s : ℝ) < arrival τ 0 j →
        jumpCount (fun n => arrival τ n j) (s : ℝ) = 0) ∧
      jumpCount (fun n => arrival τ n j) (arrival τ 0 j) = 1 := by
    filter_upwards [hPos, hCount] with j hp hc
    exact ⟨hp, hc.1, hc.2⟩
  have hEq : μ (
      {j : Ω |
        0 < τ 0 j ∧
        (∀ s : ℝ≥0, (s : ℝ) < arrival τ 0 j →
          jumpCount (fun n => arrival τ n j) (s : ℝ) = 0) ∧
        jumpCount (fun n => arrival τ n j) (arrival τ 0 j) = 1} ∩
      {j : Ω | τ 0 j ≤ horizon}) =
      μ {j : Ω | τ 0 j ≤ horizon} :=
    Measure.measure_inter_eq_of_ae hGood
  rw [hEq]
  exact hEarly
