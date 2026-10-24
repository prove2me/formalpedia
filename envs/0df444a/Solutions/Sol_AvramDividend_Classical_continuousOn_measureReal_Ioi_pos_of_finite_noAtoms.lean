-- Prove2me | solution 1 for AvramDividend.Classical.continuousOn_measureReal_Ioi_pos_of_finite_noAtoms
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-23T20:59:33.303829+00:00
-- url     : https://prove2.me/submissions/9d768ab1-8e21-4966-af4c-b3775899ef1b

import Mathlib.MeasureTheory.OuterMeasure.Basic
import Mathlib.MeasureTheory.Measure.Typeclasses.NullSingletonClass
import Theorems.Thm_AvramDividend_Classical_continuousOn_measureReal_Ici_pos_of_finite_noAtoms

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set
open scoped ENNReal

/-- Strict positive upper tails are continuous when all atoms vanish. -/
theorem solution
    (μ : Measure ℝ) [NullSingletonClass μ]
    (hfin : ∀ x : ℝ, 0 < x → μ (Ici x) ≠ ⊤) :
    ContinuousOn (fun x : ℝ => μ.real (Ioi x)) (Ioi 0) := by
  have hEq (x : ℝ) : μ (Ioi x) = μ (Ici x) := by
    have hs : Ioi x = Ici x \ {x} := by
      ext y
      simp only [mem_Ioi, mem_diff, mem_Ici, mem_singleton_iff]
      constructor
      · intro h
        exact ⟨le_of_lt h, ne_of_gt h⟩
      · rintro ⟨h, hne⟩
        exact lt_of_le_of_ne h (Ne.symm hne)
    rw [hs, measure_diff_null (measure_singleton x)]
  have hfun :
      (fun x : ℝ => μ.real (Ioi x)) =
        (fun x : ℝ => μ.real (Ici x)) := by
    funext x
    simp only [Measure.real, hEq]
  rw [hfun]
  exact continuousOn_measureReal_Ici_pos_of_finite_noAtoms μ hfin
