-- Prove2me | solution 1 for AvramDividend.Classical.avram_physical_expected_bound_to_zero_residual_mesh_certificate
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-14T09:41:12.01225+00:00
-- url     : https://prove2.me/submissions/978370a8-2216-464a-9dc7-9af8de745c7a

import Mathlib
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter
open scoped ENNReal Topology
noncomputable section

theorem solution
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (Y : ℕ → Ω → ℝ) (K : ℝ)
    (hIntegrable : ∀ n, Integrable (Y n) P)
    (hMean : ∀ n, (∫ ω, Y n ω ∂P) ≤ K) :
    ∃ M B Err : ℕ → Ω → ℝ,
      (∀ n, Integrable (fun ω => M n ω + B n ω) P ∧
        (∫ ω, M n ω + B n ω ∂P) ≤ 0) ∧
      (∀ n, Integrable (fun ω => max (Err n ω) 0) P) ∧
      Tendsto (fun n => ∫ ω, max (Err n ω) 0 ∂P) atTop (𝓝 0) ∧
      (∀ n, ∀ᵐ ω ∂P,
        Y n ω ≤ K + (M n ω + B n ω) + max (Err n ω) 0) := by
  classical
  let B : ℕ → Ω → ℝ := fun n ω => Y n ω - K
  have hBI : ∀ n, Integrable (B n) P := by
    intro n
    exact (hIntegrable n).sub (integrable_const _)
  have hBmean : ∀ n, (∫ ω, B n ω ∂P) ≤ 0 := by
    intro n
    have hEq : (∫ ω, Y n ω - K ∂P) =
        (∫ ω, Y n ω ∂P) - K := by
      rw [integral_sub (hIntegrable n) (integrable_const _)]
      simp
    change (∫ ω, Y n ω - K ∂P) ≤ 0
    rw [hEq]
    exact sub_nonpos.mpr (hMean n)
  refine ⟨(fun _ _ => 0), B, (fun _ _ => 0), ?_, ?_, ?_, ?_⟩
  · intro n
    constructor
    · simpa only [zero_add] using hBI n
    · simpa only [zero_add] using hBmean n
  · intro n
    simp
  · simp
  · intro n
    filter_upwards [] with ω
    change Y n ω ≤ K + (0 + B n ω) + max (0 : ℝ) 0
    dsimp [B]
    simp
