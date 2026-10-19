-- Prove2me | solution 1 for CohnElkies.tendsto_factorialStirlingSequence
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:34.337066+00:00
-- url     : https://prove2.me/submissions/20f2be69-572b-479a-aea4-f32d3e931659

import Mathlib
import Definitions.Def_SpherePacking

set_option autoImplicit true
open CohnElkies
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 800000
noncomputable section
open Filter
open scoped Nat Topology
namespace CohnElkies
theorem _root_.solution :
    Tendsto Stirling.stirlingSeq atTop
      (nhds (Real.sqrt Real.pi)) :=
  Stirling.tendsto_stirlingSeq_sqrt_pi
end CohnElkies
