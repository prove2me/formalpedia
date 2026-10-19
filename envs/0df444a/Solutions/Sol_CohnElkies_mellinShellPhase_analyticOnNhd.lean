-- Prove2me | solution 1 for CohnElkies.mellinShellPhase_analyticOnNhd
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:19.890976+00:00
-- url     : https://prove2.me/submissions/e122adc0-6bbf-43a6-850f-37a0a61042cf

import Mathlib
import Definitions.Def_SpherePacking

set_option autoImplicit true
open CohnElkies
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 800000
noncomputable section
open Filter Set MeasureTheory intervalIntegral
open scoped ContDiff FourierTransform Interval RealInnerProductSpace Topology
namespace CohnElkies
theorem _root_.solution {ε : ℝ}
    (hε : 0 < ε)
    (horder : shortCutoff ε ≤ shortEndpoint ε) :
    AnalyticOnNhd ℂ (mellinShellPhase ε) Set.univ :=
  Complex.analyticOnNhd_univ_iff_differentiable.mpr
    (mellinShellPhase_differentiable hε horder)
end CohnElkies
