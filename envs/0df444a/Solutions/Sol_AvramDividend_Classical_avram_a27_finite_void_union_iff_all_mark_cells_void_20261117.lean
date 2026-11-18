-- Prove2me | solution 1 for AvramDividend.Classical.avram_a27_finite_void_union_iff_all_mark_cells_void_20261117
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-17T17:18:36.5706+00:00
-- url     : https://prove2.me/submissions/6536dfef-e607-4dbc-986c-48ae33ebae26

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
noncomputable section

/-- A finite union is null exactly when each member set is null for any source measure. -/
theorem solution
    {α ι : Type*} [MeasurableSpace α] [DecidableEq ι]
    (μ : Measure α) (S : Finset ι) (B : ι → Set α) :
    μ (⋃ i ∈ S, B i) = 0 ↔ ∀ i ∈ S, μ (B i) = 0 := by
  classical
  induction S using Finset.induction_on with
  | empty => simp
  | @insert a S ha ih =>
      simp only [Finset.set_biUnion_insert, measure_union_null_iff,
        ih, Finset.forall_mem_insert]
