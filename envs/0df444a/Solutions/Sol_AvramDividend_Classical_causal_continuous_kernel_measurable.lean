-- Prove2me | solution 1 for AvramDividend.Classical.causal_continuous_kernel_measurable
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-24T16:44:29.198991+00:00
-- url     : https://prove2.me/submissions/e7348392-7c9a-4196-a27d-50d6d7c1aa04

import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
import Mathlib.Topology.ContinuousOn
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set

/-- Causality and continuity off the origin give global kernel measurability. -/
theorem solution
    (k : ℝ → ℝ)
    (hkcont : ContinuousOn k (Ioi (0 : ℝ)))
    (hkzero : ∀ x : ℝ, x ≤ 0 → k x = 0) :
    Measurable k := by
  classical
  let s : Set ℝ := Ioi (0 : ℝ)
  have hzeroCont : ContinuousOn (fun _ : ℝ => (0 : ℝ)) sᶜ :=
    continuous_const.continuousOn
  have hmeas : Measurable (s.piecewise k (fun _ : ℝ => 0)) :=
    hkcont.measurable_piecewise hzeroCont measurableSet_Ioi
  have heq : s.piecewise k (fun _ : ℝ => 0) = k := by
    funext x
    by_cases hx : 0 < x
    · simp [s, Set.piecewise, hx]
    · have hle : x ≤ 0 := le_of_not_gt hx
      simp [s, Set.piecewise, hx, hkzero x hle]
  simpa only [heq] using hmeas
