-- Prove2me | solution 1 for CohnElkies.upperCenteredLaplaceKernel_integrable
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:29.488992+00:00
-- url     : https://prove2.me/submissions/19623c2e-0121-4460-831a-6f1bd3c1e735

import Mathlib
import Definitions.Def_SpherePacking
import Theorems.Thm_CohnElkies_complexLaplaceKernel_integrable
import Theorems.Thm_CohnElkies_complexFrullaniKernel_integrable
import Theorems.Thm_CohnElkies_upperCenteredLaplaceKernel_eq_frullani_sub_laplace

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
    {c : ℝ} (hc : 0 < c) (T : ℝ) :
    IntegrableOn (upperCenteredLaplaceKernel c T)
      (Ioi 0) := by
  let z : ℂ := (c : ℂ) - Complex.I * (T : ℂ)
  let w : ℂ := (c : ℂ)
  have hz : 0 < z.re := by simpa [z] using! hc
  have hw : 0 < w.re := by simpa [w] using! hc
  have hfrullani := complexFrullaniKernel_integrable hz hw
  have hlaplace :=
    (complexLaplaceKernel_integrable hw).const_mul
      (Complex.I * (T : ℂ))
  apply (hfrullani.sub hlaplace).congr
  filter_upwards [ae_restrict_mem measurableSet_Ioi]
    with a ha
  exact (upperCenteredLaplaceKernel_eq_frullani_sub_laplace
    c T ha.ne').symm
end CohnElkies
