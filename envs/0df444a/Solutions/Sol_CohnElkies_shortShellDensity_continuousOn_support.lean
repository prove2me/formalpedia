-- Prove2me | solution 1 for CohnElkies.shortShellDensity_continuousOn_support
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:27.275309+00:00
-- url     : https://prove2.me/submissions/2126ebe2-b445-4c64-82dd-a1527876e349

import Mathlib
import Definitions.Def_SpherePacking

set_option autoImplicit true
open CohnElkies
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 800000
noncomputable section
open Filter MeasureTheory Set
open scoped Topology
namespace CohnElkies
theorem _root_.solution
    {ε : ℝ} (hε : 0 < ε) :
    ContinuousOn (shortShellDensity ε)
      (Icc (shortCutoff ε) (shortEndpoint ε)) := by
  have hn : Continuous
      (fun a : ℝ =>
        shortMargin ε a * Real.exp (-2 * a)) := by
    unfold shortMargin
    fun_prop
  have hd : Continuous
      (fun a : ℝ =>
        2 * a ^ 2 * Real.cosh a) := by
    fun_prop
  unfold shortShellDensity
  exact (hn.continuousOn.div hd.continuousOn
    (fun a ha => by
      have hcutoff : 0 < shortCutoff ε := by
        unfold shortCutoff
        positivity
      have ha0 : 0 < a := hcutoff.trans_le ha.1
      positivity)).neg
end CohnElkies
