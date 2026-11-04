-- Prove2me | solution 1 for AvramDividend.Classical.avram_p2_c_borel_cutoff_dense_below_ext
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T13:27:27.431533+00:00
-- url     : https://prove2.me/submissions/f1062d5f-fa56-46b3-b696-fa7143f772a7

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_p2_c_borel_cutoff_dense_halfline_ext

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter Topology
open scoped ENNReal

/-- Dense tests strictly below a finite cutoff, plus its total, determine the Borel restriction. -/
theorem solution
    (μ ν : Measure ℝ) (c : ℝ)
    (hμfin : μ (Iic c) ≠ ⊤) (hνfin : ν (Iic c) ≠ ⊤)
    (D : Set ℝ) (hDense : Dense D)
    (hCut : μ (Iic c) = ν (Iic c))
    (hTests : ∀ a : ℝ, a ∈ D → a < c → μ (Iic a) = ν (Iic a)) :
    μ.restrict (Iic c) = ν.restrict (Iic c) := by
  apply AvramDividend.Classical.avram_p2_c_borel_cutoff_dense_halfline_ext
    μ ν c hμfin hνfin D hDense
  intro a ha
  by_cases hac : a < c
  · have hSmall : Iic a ∩ Iic c = Iic a := by
      ext x
      simp only [mem_inter_iff, mem_Iic]
      constructor
      · exact And.left
      · intro hxa
        exact ⟨hxa, le_trans hxa (le_of_lt hac)⟩
    simpa only [hSmall] using hTests a ha hac
  · have hBig : Iic a ∩ Iic c = Iic c := by
      ext x
      simp only [mem_inter_iff, mem_Iic]
      constructor
      · exact And.right
      · intro hxc
        exact ⟨le_trans hxc (le_of_not_gt hac), hxc⟩
    simpa only [hBig] using hCut
