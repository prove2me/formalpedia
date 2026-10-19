-- Prove2me | solution 1 for CohnElkies.complexWallisPhaseKernel_integrable
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:24.652437+00:00
-- url     : https://prove2.me/submissions/beebe534-1d48-49e0-a3bf-aadb9053f43b

import Mathlib
import Definitions.Def_SpherePacking
import Theorems.Thm_CohnElkies_complexFrullaniShiftParameter_integrable
import Theorems.Thm_CohnElkies_intervalIntegral_complexFrullaniShift

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
    {z : ℂ} (hz : 0 < z.re) :
    IntegrableOn (complexWallisPhaseKernel z) (Ioi 0) := by
  have hproduct :=
    (complexFrullaniShiftParameter_integrable hz).integral_prod_right
  apply hproduct.congr
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
  change
    (∫ s in Set.uIoc (0 : ℝ) 1,
      complexFrullaniKernel (z + (s : ℂ)) 1 x) =
      complexWallisPhaseKernel z x
  rw [Set.uIoc_of_le (show (0 : ℝ) ≤ 1 by norm_num),
    ← intervalIntegral.integral_of_le
      (show (0 : ℝ) ≤ 1 by norm_num)]
  exact intervalIntegral_complexFrullaniShift z hx.ne'
end CohnElkies
