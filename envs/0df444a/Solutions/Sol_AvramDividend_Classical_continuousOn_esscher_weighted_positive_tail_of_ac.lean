-- Prove2me | solution 1 for AvramDividend.Classical.continuousOn_esscher_weighted_positive_tail_of_ac
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-24T17:52:51.466361+00:00
-- url     : https://prove2.me/submissions/2fe54bde-d473-413a-9e59-bdb7c895074d

import Mathlib.MeasureTheory.Measure.AbsolutelyContinuous
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Theorems.Thm_AvramDividend_Classical_continuousOn_positive_strict_tail_of_absolutelyContinuous

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set
open scoped ENNReal

/-- Weighted absolute continuity transfers the positive strict-tail
continuity theorem to the Esscher-discounted measure. -/
theorem solution
    (μ : Measure ℝ) (hac : μ ≪ volume) (φ : ℝ)
    (hfin : ∀ x : ℝ, 0 < x →
      (μ.withDensity
        (fun z : ℝ => ENNReal.ofReal (Real.exp (-(φ * z))))) (Ici x) ≠ ⊤) :
    ContinuousOn
      (fun x : ℝ =>
        (μ.withDensity
          (fun z : ℝ => ENNReal.ofReal (Real.exp (-(φ * z))))).real (Ioi x))
      (Ioi (0 : ℝ)) := by
  have hweight :
      μ.withDensity
        (fun z : ℝ => ENNReal.ofReal (Real.exp (-(φ * z)))) ≪ volume :=
    (withDensity_absolutelyContinuous _ _).trans hac
  exact continuousOn_positive_strict_tail_of_absolutelyContinuous
    _ hweight hfin
