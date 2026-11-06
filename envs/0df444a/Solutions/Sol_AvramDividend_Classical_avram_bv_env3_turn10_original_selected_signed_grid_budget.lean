-- Prove2me | solution 1 for AvramDividend.Classical.avram_bv_env3_turn10_original_selected_signed_grid_budget
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-05T23:02:51.804969+00:00
-- url     : https://prove2.me/submissions/b0b1fbf3-79f0-4a80-a7c0-30438cdd30cf

import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Theorems.Thm_AvramDividend_Classical_avram_bv_env3_turn9_integrable_bounded_measurable_source_prefix
import Theorems.Thm_AvramDividend_Classical_avram_bv_env3_turn9_original_centered_stopped_source_prefix_mean_zero
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
noncomputable section

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] (P : Measure Ω)
    (m : ℕ) (k : Ω → ℕ)
    (hk : Measurable k) (hkBound : ∀ ω, k ω ≤ m)
    (M B : ℕ → Ω → ℝ)
    (hMI : ∀ i, Integrable (M i) P)
    (hBI : ∀ i, Integrable (B i) P)
    (hMean : ∀ i < m, (∫ ω, (if i < k ω then M i ω else 0) ∂P) = 0)
    (hDrift : ∀ i ω, B i ω ≤ 0) :
    Integrable (fun ω => ∑ i ∈ Finset.range (k ω), (M i ω + B i ω)) P ∧
    (∫ ω, ∑ i ∈ Finset.range (k ω), (M i ω + B i ω) ∂P) ≤ 0 := by
  classical
  have hIntM :=
    avram_bv_env3_turn9_integrable_bounded_measurable_source_prefix
      P m k hk hkBound M hMI
  have hIntB :=
    avram_bv_env3_turn9_integrable_bounded_measurable_source_prefix
      P m k hk hkBound B hBI
  have hZero :=
    avram_bv_env3_turn9_original_centered_stopped_source_prefix_mean_zero
      P m k hk hkBound M hMI hMean
  have hSign : ∀ ω, ∑ i ∈ Finset.range (k ω), B i ω ≤ 0 := by
    intro ω
    apply Finset.sum_nonpos
    intro i hi
    exact hDrift i ω
  have hBInt : (∫ ω, ∑ i ∈ Finset.range (k ω), B i ω ∂P) ≤ 0 :=
    integral_nonpos hSign
  have hSplit : (fun ω : Ω =>
      ∑ i ∈ Finset.range (k ω), (M i ω + B i ω)) =
      (fun ω : Ω =>
        (∑ i ∈ Finset.range (k ω), M i ω) +
        (∑ i ∈ Finset.range (k ω), B i ω)) := by
    funext ω
    exact Finset.sum_add_distrib
  rw [hSplit]
  constructor
  · exact hIntM.add hIntB
  · rw [integral_add hIntM hIntB, hZero]
    simpa using hBInt
