-- Prove2me | solution 1 for AvramDividend.Classical.chat03_uniformIntegrable_of_pointwise_bounded_family
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-19T22:36:10.719929+00:00
-- url     : https://prove2.me/submissions/7c0e07c2-c9cd-4bb0-ad00-d3f0c6bb9e8f

import Mathlib.MeasureTheory.Function.UniformIntegrable
import Mathlib.Tactic.NormNum

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped ENNReal NNReal

/-!
A single pointwise bound on a measurable family gives uniform
integrability in L1. This is the bounded no-passage branch's
uniform-integrability interface for the stopped-scale programme.
-/
theorem solution
    {Ω ι : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsFiniteMeasure μ]
    (f : ι → Ω → ℝ)
    (hf : ∀ i, AEStronglyMeasurable (f i) μ)
    (K : ℝ≥0)
    (hbound : ∀ i ω, ‖f i ω‖₊ ≤ K) :
    UniformIntegrable f (1 : ℝ≥0∞) μ := by
  apply uniformIntegrable_of (by norm_num) (by norm_num) hf
  intro ε hε
  refine ⟨K + 1, ?_⟩
  intro i
  have htail : {ω : Ω | K + 1 ≤ ‖f i ω‖₊} = ∅ := by
    ext ω
    simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
    exact not_le.mpr
      ((hbound i ω).trans_lt (lt_add_of_pos_right K zero_lt_one))
  simp [htail]
