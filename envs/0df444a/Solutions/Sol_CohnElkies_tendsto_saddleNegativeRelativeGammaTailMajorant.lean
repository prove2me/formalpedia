-- Prove2me | solution 1 for CohnElkies.tendsto_saddleNegativeRelativeGammaTailMajorant
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:27.981105+00:00
-- url     : https://prove2.me/submissions/5d4c3fbf-8a86-4a46-9bfc-3acecf6886d0

import Mathlib
import Definitions.Def_SpherePacking
import Theorems.Thm_CohnElkies_tendsto_saddleNegativeTruncation_odd_sq_div
import Theorems.Thm_CohnElkies_tendsto_saddleNegativeLogWindowTailMajorant

set_option autoImplicit true
open CohnElkies
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 800000
noncomputable section
open Filter Set MeasureTheory
open scoped Topology BigOperators
namespace CohnElkies
theorem _root_.solution
    (C K Kε : ℝ) :
    Tendsto (saddleNegativeRelativeGammaTailMajorant C K Kε)
      atTop (𝓝 0) := by
  have hsmall :=
    tendsto_saddleNegativeLogWindowTailMajorant C
  have herror :=
    (tendsto_saddleNegativeTruncation_odd_sq_div.const_mul K).rexp
  have htotal :=
    (hsmall.const_mul
      (2 * Kε / Real.Gamma (3 / 2 : ℝ))).mul herror
  convert! htotal using 1
  · funext ℓ
    unfold saddleNegativeRelativeGammaTailMajorant
    ring_nf
  · norm_num
end CohnElkies
