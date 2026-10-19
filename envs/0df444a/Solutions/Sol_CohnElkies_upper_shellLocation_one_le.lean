-- Prove2me | solution 1 for CohnElkies.upper_shellLocation_one_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:26.273981+00:00
-- url     : https://prove2.me/submissions/bf340248-a832-4a80-a754-5ced97adcc1a

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
    {ε : ℝ} (hε : 0 < ε) (hεone : ε ≤ 1) :
    1 ≤ shellLocation ε := by
  have hinv : 1 ≤ ε⁻¹ :=
    (one_le_inv₀ hε).mpr hεone
  unfold shellLocation
  convert! pow_le_pow_left₀
    (show (0 : ℝ) ≤ 1 by norm_num) hinv 3 using 1; norm_num
end CohnElkies
