-- Prove2me | solution 1 for CohnElkies.upperCosLaplaceKernel_integrable
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:27.981105+00:00
-- url     : https://prove2.me/submissions/39dbe0c6-f0f0-4d34-a08e-c177efa1987f

import Mathlib
import Definitions.Def_SpherePacking
import Theorems.Thm_CohnElkies_complexFrullaniKernel_integrable
import Theorems.Thm_CohnElkies_upperCosLaplaceKernel_eq_frullani_re

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
    IntegrableOn (upperCosLaplaceKernel c T) (Ioi 0) := by
  have hw : 0 < ((c : ℂ) + Complex.I * (T : ℂ)).re := by
    simpa using! hc
  have h := complexFrullaniKernel_integrable (z := (c : ℂ))
    (w := (c : ℂ) + Complex.I * (T : ℂ)) (by simpa using! hc) hw
  have hr := h.re
  exact hr.congr (Filter.Eventually.of_forall
    (fun a => (upperCosLaplaceKernel_eq_frullani_re c T a).symm))
end CohnElkies
