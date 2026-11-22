-- Prove2me | solution 1 for AvramDividend.Classical.avram_oai_nonpositive_bounded_simple_quantizer_uniform_range_20261122
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-22T14:48:50.322855+00:00
-- url     : https://prove2.me/submissions/127a9805-9877-4a8f-b130-ac509d7a9165

import Mathlib.MeasureTheory.Function.SimpleFuncDense
open MeasureTheory Set Filter
open scoped Topology
noncomputable section
set_option autoImplicit false

theorem solution :
    ∃ f : ℕ → SimpleFunc ℝ ℝ,
      (∀ k z, f k z ∈ Icc (-1 : ℝ) 0) ∧
      (∀ z ∈ Icc (-1 : ℝ) 0,
        Tendsto (fun k => f k z) atTop (𝓝 z))  := by
  classical
  let s : Set ℝ := Icc (-1 : ℝ) 0
  have hzero : (0 : ℝ) ∈ s := by simp [s]
  let f : ℕ → SimpleFunc ℝ ℝ := fun k =>
    SimpleFunc.approxOn id measurable_id s 0 hzero k
  refine ⟨f, ?_, ?_⟩
  · intro k z
    exact SimpleFunc.approxOn_mem measurable_id hzero k z
  · intro z hz
    have hmem : z ∈ closure s := subset_closure hz
    simpa [f, id_eq] using
      (SimpleFunc.tendsto_approxOn measurable_id hzero hmem)
