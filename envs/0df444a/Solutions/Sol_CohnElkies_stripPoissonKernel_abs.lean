-- Prove2me | solution 1 for CohnElkies.stripPoissonKernel_abs
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:21.360486+00:00
-- url     : https://prove2.me/submissions/c26f9c0e-0cd3-4203-976b-9d2a2a16be7a

import Mathlib
import Definitions.Def_SpherePacking
import Theorems.Thm_CohnElkies_stripPoissonKernel_neg

set_option autoImplicit true
open CohnElkies
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 800000
noncomputable section
open Filter MeasureTheory Set
open scoped Interval Topology
namespace CohnElkies
theorem _root_.solution (σ T : ℝ) :
    stripPoissonKernel σ |T| = stripPoissonKernel σ T := by
  rcases le_total 0 T with h | h
  · rw [abs_of_nonneg h]
  · rw [abs_of_nonpos h, stripPoissonKernel_neg]
end CohnElkies
