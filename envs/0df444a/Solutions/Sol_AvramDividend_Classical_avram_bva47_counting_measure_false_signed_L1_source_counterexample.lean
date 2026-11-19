-- Prove2me | solution 1 for AvramDividend.Classical.avram_bva47_counting_measure_false_signed_L1_source_counterexample
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-18T07:30:52.397046+00:00
-- url     : https://prove2.me/submissions/69970d12-a8c7-497b-a1c9-984fb586cc27

import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Mathlib.MeasureTheory.Measure.Count
import Mathlib.MeasureTheory.Function.L1Space.Integrable
import Mathlib.Tactic.NormNum
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

set_option autoImplicit false
open Classical MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

theorem solution :
    ∃ (F M B E : ℕ → ℝ) (a : ℝ),
      Integrable F (Measure.count : Measure ℕ) ∧
      Integrable M (Measure.count : Measure ℕ) ∧
      Integrable (fun ω => max (E ω) 0) (Measure.count : Measure ℕ) ∧
      AEStronglyMeasurable B (Measure.count : Measure ℕ) ∧
      (∀ᵐ ω ∂(Measure.count : Measure ℕ), B ω ≤ 0) ∧
      (∀ᵐ ω ∂(Measure.count : Measure ℕ),
        F ω ≤ a + M ω + B ω + max (E ω) 0) ∧
      ¬ Integrable B (Measure.count : Measure ℕ) := by
  refine ⟨(fun _ : ℕ => (0 : ℝ)), (fun _ => 0), (fun _ => -1),
    (fun _ => 0), 1, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simpa using
      (integrable_zero (Measure.count : Measure ℕ) :
        Integrable (0 : ℕ → ℝ) (Measure.count : Measure ℕ))
  · simpa using
      (integrable_zero (Measure.count : Measure ℕ) :
        Integrable (0 : ℕ → ℝ) (Measure.count : Measure ℕ))
  · simpa using
      (integrable_zero (Measure.count : Measure ℕ) :
        Integrable (0 : ℕ → ℝ) (Measure.count : Measure ℕ))
  · exact aestronglyMeasurable_const
  · filter_upwards [] with ω
    norm_num
  · filter_upwards [] with ω
    norm_num
  · intro hInt
    have hFin : IsFiniteMeasure (Measure.count : Measure ℕ) := by
      have h := (integrable_const_iff.mp hInt)
      rcases h with hZero | hFinite
      · norm_num at hZero
      · exact hFinite
    have hInf : ¬ IsFiniteMeasure (Measure.count : Measure ℕ) := by
      rw [not_isFiniteMeasure_iff]
      simp
    exact hInf hFin
