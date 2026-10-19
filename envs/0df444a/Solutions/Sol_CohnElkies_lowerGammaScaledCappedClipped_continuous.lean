-- Prove2me | solution 1 for CohnElkies.lowerGammaScaledCappedClipped_continuous
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:33.627368+00:00
-- url     : https://prove2.me/submissions/50683d99-69bc-4ac2-b044-43017be7090f

import Mathlib
import Definitions.Def_SpherePacking
import Theorems.Thm_CohnElkies_lowerGammaBoundaryCapped_continuous

set_option autoImplicit true
open CohnElkies
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 800000
noncomputable section
open Filter MeasureTheory Metric Set
open scoped ENNReal Interval Topology
namespace CohnElkies
theorem _root_.solution
    {d : ℕ} (hd : 0 < d) (c D n : ℝ) :
    Continuous (lowerGammaScaledCappedClipped d c D n) := by
  have hℓ : 0 < (d : ℝ) / 2 :=
    half_pos (Nat.cast_pos.mpr hd)
  have hcap := lowerGammaBoundaryCapped_continuous
    hℓ (c * Real.sqrt d) D
  have hscale : Continuous (fun Y : ℝ => ((d : ℝ) / 2) * Y) := by
    fun_prop
  exact ((hcap.comp hscale).add continuous_const).max
    continuous_const
end CohnElkies
