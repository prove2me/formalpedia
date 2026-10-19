-- Prove2me | solution 1 for CohnElkies.upperCosLaplaceKernel_eq_frullani_re
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:27.981105+00:00
-- url     : https://prove2.me/submissions/c2b22d2b-7c92-4078-956c-b792ff8f3561

import Mathlib
import Definitions.Def_SpherePacking

set_option autoImplicit true
open CohnElkies
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 800000
noncomputable section
open Filter MeasureTheory Set
open scoped Topology BigOperators
namespace CohnElkies
theorem _root_.solution
    (c T a : ℝ) :
    upperCosLaplaceKernel c T a =
      (complexFrullaniKernel (c : ℂ)
        ((c : ℂ) + Complex.I * (T : ℂ)) a).re := by
  simp [upperCosLaplaceKernel, complexFrullaniKernel,
    Complex.exp_re, Real.cos_neg]
  ring_nf
end CohnElkies
