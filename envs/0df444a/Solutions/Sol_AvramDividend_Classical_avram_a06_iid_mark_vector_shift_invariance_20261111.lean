-- Prove2me | solution 1 for AvramDividend.Classical.avram_a06_iid_mark_vector_shift_invariance_20261111
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-11T19:19:07.827208+00:00
-- url     : https://prove2.me/submissions/837b552b-708d-490f-9309-e2913630a8ee

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_a06_finite_independent_identDistrib_joint_law_20261111
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory
noncomputable section

/-- The joint law of a finite IID window is translation invariant. -/
theorem solution
    {Ω A : Type*} [MeasurableSpace Ω] [MeasurableSpace A]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (Y : ℕ → Ω → A) (hY : ∀ j, Measurable (Y j))
    (hInd : iIndepFun Y P)
    (hSame : ∀ j k, IdentDistrib (Y j) (Y k) P P)
    (a k : ℕ) :
    IdentDistrib (fun ω => fun i : Fin k => Y (a + i.val) ω)
      (fun ω => fun i : Fin k => Y i.val ω) P P := by
  let U : Fin k → Ω → A := fun i => Y (a + i.val)
  let V : Fin k → Ω → A := fun i => Y i.val
  have hU : iIndepFun U P := hInd.precomp (by
    intro i j h
    apply Fin.ext
    exact Nat.add_left_cancel h)
  have hV : iIndepFun V P := hInd.precomp (by
    intro i j h
    exact Fin.ext h)
  exact AvramDividend.Classical.avram_a06_finite_independent_identDistrib_joint_law_20261111
    P k U V (fun i => hY (a + i.val)) (fun i => hY i.val)
    hU hV (fun i => hSame (a + i.val) i.val)
