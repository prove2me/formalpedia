-- Prove2me | solution 1 for CohnElkies.tendsto_saddleNegativeTruncation_odd_sq_div
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:27.981105+00:00
-- url     : https://prove2.me/submissions/7ff13566-daa6-494b-993c-6a9635a35152

import Mathlib
import Definitions.Def_SpherePacking
import Theorems.Thm_CohnElkies_tendsto_saddleSmallResidueTruncation_div
import Theorems.Thm_CohnElkies_tendsto_saddleSmallResidueTruncation_sq_div

set_option autoImplicit true
open CohnElkies
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 800000
noncomputable section
open Filter Set MeasureTheory
open scoped Topology BigOperators
namespace CohnElkies
theorem _root_.solution :
    Tendsto
      (fun ℓ : ℝ =>
        (2 * (saddleSmallResidueTruncation ℓ : ℝ) + 1) ^ 2 / ℓ)
      atTop (𝓝 0) := by
  have hinv : Tendsto
      (fun ℓ : ℝ => (1 : ℝ) / ℓ)
      atTop (𝓝 0) := by
    simpa [one_div] using!
      (tendsto_inv_atTop_zero :
        Tendsto (fun ℓ : ℝ => ℓ⁻¹) atTop (𝓝 0))
  have h :=
    ((tendsto_saddleSmallResidueTruncation_sq_div.const_mul 4).add
      (tendsto_saddleSmallResidueTruncation_div.const_mul 4)).add
        hinv
  convert! h using 1
  · funext ℓ
    ring
  · norm_num
end CohnElkies
