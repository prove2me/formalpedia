-- Prove2me | solution 1 for AvramDividend.Classical.avram_p2_c_borel_restrict_halfline_nonatom_ext
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T12:42:05.255938+00:00
-- url     : https://prove2.me/submissions/453c7f1b-067a-4871-bbf6-393f13818a94

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_p2_c_borel_finite_measure_ext_of_nonatom_halfline_tests

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped ENNReal

/-- Nonatom tests below a finite cutoff determine a restricted Borel measure. -/
theorem solution
    (μ ν : Measure ℝ) (c : ℝ)
    (hμfin : μ (Iic c) ≠ ⊤) (hνfin : ν (Iic c) ≠ ⊤)
    (hcut : μ (Iic c) = ν (Iic c))
    (htests : ∀ a : ℝ, a < c → ν {a} = 0 → μ (Iic a) = ν (Iic a)) :
    μ.restrict (Iic c) = ν.restrict (Iic c) := by
  haveI : IsFiniteMeasure (μ.restrict (Iic c)) :=
    (isFiniteMeasure_restrict).2 hμfin
  haveI : IsFiniteMeasure (ν.restrict (Iic c)) :=
    (isFiniteMeasure_restrict).2 hνfin
  apply AvramDividend.Classical.avram_p2_c_borel_finite_measure_ext_of_nonatom_halfline_tests
  intro a ha
  by_cases hac : a < c
  · have hSingle : ({a} : Set ℝ) ∩ Iic c = {a} := by
      ext x
      simp only [mem_inter_iff, mem_singleton_iff, mem_Iic]
      constructor
      · exact And.left
      · intro hxa
        exact ⟨hxa, hxa ▸ le_of_lt hac⟩
    have hAtom : ν {a} = 0 := by
      simpa only [Measure.restrict_apply (measurableSet_singleton a), hSingle] using ha
    have hSmall : Iic a ∩ Iic c = Iic a := by
      ext x
      simp only [mem_inter_iff, mem_Iic]
      constructor
      · exact And.left
      · intro hxa
        exact ⟨hxa, le_trans hxa (le_of_lt hac)⟩
    simpa only [Measure.restrict_apply measurableSet_Iic, hSmall] using
      (htests a hac hAtom)
  · have hBig : Iic a ∩ Iic c = Iic c := by
      ext x
      simp only [mem_inter_iff, mem_Iic]
      constructor
      · exact And.right
      · intro hxc
        exact ⟨le_trans hxc (le_of_not_gt hac), hxc⟩
    simpa only [Measure.restrict_apply measurableSet_Iic, hBig] using hcut
