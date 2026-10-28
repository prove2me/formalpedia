-- Prove2me | solution 1 for AvramDividend.Classical.affine_cutoff_continuous_nonnegative_smooth_positive
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-26T21:29:17.883236+00:00
-- url     : https://prove2.me/submissions/0684a9ae-0789-42bd-9072-b09ef6ae28e3

import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Topology.Order.Basic
import Mathlib.Tactic

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Set

theorem solution :
    ContinuousOn (fun z : ℝ => if z < 0 then 0 else z - 1) (Ici (0 : ℝ)) ∧
    ContDiffOn ℝ 2 (fun z : ℝ => if z < 0 then 0 else z - 1) (Ioi (0 : ℝ)) := by
  constructor
  · have hc : ContinuousOn (fun z : ℝ => z - 1) (Ici (0 : ℝ)) :=
      (continuous_id.sub continuous_const).continuousOn
    apply hc.congr
    intro z hz
    change 0 ≤ z at hz
    simp [not_lt.mpr hz]
  · have hid : ContDiff ℝ 2 (fun z : ℝ => z) := contDiff_id
    have hconst : ContDiff ℝ 2 (fun _ : ℝ => (1 : ℝ)) := contDiff_const
    have hc : ContDiffOn ℝ 2 (fun z : ℝ => z - 1) (Ioi (0 : ℝ)) :=
      (hid.sub hconst).contDiffOn
    apply hc.congr
    intro z hz
    change 0 < z at hz
    simp [not_lt.mpr (le_of_lt hz)]
