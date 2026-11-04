-- Prove2me | solution 1 for AvramDividend.Classical.avram_p2_c_borel_cutoff_dense_ext_from_comparator_finite
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T13:15:49.699916+00:00
-- url     : https://prove2.me/submissions/1c947fac-3527-4530-b2c6-87ef57798a3f

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_p2_c_borel_cutoff_dense_halfline_ext

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter Topology
open scoped ENNReal

/-- Finiteness of the source cutoff measure follows from dense tests against a finite comparator. -/
theorem solution
    (μ ν : Measure ℝ) (c : ℝ)
    (hνfin : ν (Iic c) ≠ ⊤)
    (D : Set ℝ) (hDense : Dense D)
    (hTests : ∀ a : ℝ, a ∈ D → μ (Iic a ∩ Iic c) = ν (Iic a ∩ Iic c)) :
    μ.restrict (Iic c) = ν.restrict (Iic c) := by
  obtain ⟨q, _, hMem, _⟩ := hDense.exists_seq_strictAnti_tendsto c
  have hcq : c ≤ q 0 := le_of_lt (hMem 0).1
  have hLarge : Iic (q 0) ∩ Iic c = Iic c := by
    ext x
    simp only [mem_inter_iff, mem_Iic]
    constructor
    · exact And.right
    · intro hxc
      exact ⟨le_trans hxc hcq, hxc⟩
  have hCut : μ (Iic c) = ν (Iic c) := by
    simpa only [hLarge] using hTests (q 0) (hMem 0).2
  have hμfin : μ (Iic c) ≠ ⊤ := by
    rw [hCut]
    exact hνfin
  exact AvramDividend.Classical.avram_p2_c_borel_cutoff_dense_halfline_ext
    μ ν c hμfin hνfin D hDense hTests
