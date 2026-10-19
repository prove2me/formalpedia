-- Prove2me | solution 2 for CohnElkies.tendsto_manuscriptBinaryExponentError
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-19T12:01:50.254842+00:00
-- url     : https://prove2.me/submissions/7f2d9453-64a4-4abf-8f0d-a0ab9e00928f

import Mathlib
import Definitions.Def_SpherePacking
set_option autoImplicit true
open CohnElkies
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 800000
noncomputable section
open Filter
open scoped Topology


theorem solution
    (hbinary : SharpBinaryLogAsymptotic) :
    Tendsto manuscriptBinaryExponentError atTop (nhds (0 : ℝ)) := by
  have := (hbinary.neg).sub (tendsto_const_nhds (x := criticalBinaryExponent))
  show Tendsto (fun d : ℕ => -(Real.logb 2 (linearProgram d) / (d : ℝ)) - criticalBinaryExponent) atTop (nhds 0)
  simpa using this

