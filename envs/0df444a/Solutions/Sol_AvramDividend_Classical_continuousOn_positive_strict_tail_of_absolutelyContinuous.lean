-- Prove2me | solution 1 for AvramDividend.Classical.continuousOn_positive_strict_tail_of_absolutelyContinuous
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-23T21:15:51.615576+00:00
-- url     : https://prove2.me/submissions/bf62e814-89b4-401d-84d0-2300eb6beb23

import Mathlib.MeasureTheory.Measure.AbsolutelyContinuous
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Theorems.Thm_AvramDividend_Classical_continuousOn_measureReal_Ioi_pos_of_finite_noAtoms
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set

/-- Absolute continuity removes jump atoms, hence strict tail masses vary continuously. -/
theorem solution
    (μ : Measure ℝ) (hac : μ ≪ volume)
    (hfin : ∀ x : ℝ, 0 < x → μ (Ici x) ≠ ⊤) :
    ContinuousOn (fun x : ℝ => μ.real (Ioi x)) (Ioi 0) := by
  letI : NullSingletonClass μ := ⟨fun x => hac (measure_singleton x)⟩
  exact continuousOn_measureReal_Ioi_pos_of_finite_noAtoms μ hfin
