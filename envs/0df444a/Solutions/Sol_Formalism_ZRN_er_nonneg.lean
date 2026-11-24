-- Prove2me | solution 1 for Formalism.ZRN.er_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T11:43:14.105502+00:00
-- url     : https://prove2.me/submissions/beffd64b-48b8-4526-9bf9-3b81887181e8

import Definitions.Def_Formalism_ZetaRealNonvanish
import Definitions.Def_Formalism_ZetaNonvanishing_ZetaRealNonvanish

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex Set Filter Topology
noncomputable section
open Formalism
open Formalism.ZRN
namespace Formalism.ZRN
theorem _root_.solution (n : ℕ) (σ : ℝ) (h0 : 0 < σ) (h1 : σ < 1) : 0 ≤ er n σ := by
  have hx0 : 0 < (n : ℝ) + 1 := by positivity
  have hi : 0 < ((n : ℝ) + 1)⁻¹ := inv_pos.mpr hx0
  have h2 : (n : ℝ) + 2 = ((n : ℝ) + 1) * (1 + ((n : ℝ) + 1)⁻¹) := by field_simp; ring
  have hb := rpow_one_add_le_one_add_mul_self (s := ((n : ℝ) + 1)⁻¹) (by linarith)
    (p := 1 - σ) (by linarith) (by linarith)
  have hm : ((n : ℝ) + 2) ^ (1 - σ) = ((n : ℝ) + 1) ^ (1 - σ) * (1 + ((n : ℝ) + 1)⁻¹) ^ (1 - σ) := by
    rw [h2, Real.mul_rpow hx0.le (by positivity)]
  have hs : ((n : ℝ) + 1) ^ (-σ) = ((n : ℝ) + 1) ^ (1 - σ) * ((n : ℝ) + 1)⁻¹ := by
    rw [show -σ = (1 - σ) - 1 by ring, Real.rpow_sub_one hx0.ne', div_eq_mul_inv]
  have hxp : 0 < ((n : ℝ) + 1) ^ (1 - σ) := Real.rpow_pos_of_pos hx0 _
  have := mul_le_mul_of_nonneg_left hb hxp.le
  unfold er
  rw [hm, hs]
  nlinarith
end Formalism.ZRN
