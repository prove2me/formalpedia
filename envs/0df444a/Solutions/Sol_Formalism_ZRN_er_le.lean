-- Prove2me | solution 1 for Formalism.ZRN.er_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T11:43:13.428387+00:00
-- url     : https://prove2.me/submissions/035f35a1-c7ff-4c7f-862b-da4017110dc5

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
theorem _root_.solution (n : ℕ) (σ : ℝ) (h0 : 0 < σ) (h1 : σ < 1) :
    er n σ ≤ (1 - σ) * (((n : ℝ) + 1) ^ (-σ) - ((n : ℝ) + 2) ^ (-σ)) := by
  have hy0 : 0 < (n : ℝ) + 2 := by positivity
  have hyi : ((n : ℝ) + 2)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (by have := n.cast_nonneg (α := ℝ); linarith)
  have h2 : (n : ℝ) + 1 = ((n : ℝ) + 2) * (1 + -((n : ℝ) + 2)⁻¹) := by field_simp; ring
  have hb := rpow_one_add_le_one_add_mul_self (s := -((n : ℝ) + 2)⁻¹) (by linarith)
    (p := 1 - σ) (by linarith) (by linarith)
  have hpos : 0 ≤ 1 + -((n : ℝ) + 2)⁻¹ := by linarith
  have hm : ((n : ℝ) + 1) ^ (1 - σ) = ((n : ℝ) + 2) ^ (1 - σ) * (1 + -((n : ℝ) + 2)⁻¹) ^ (1 - σ) := by
    rw [h2, Real.mul_rpow hy0.le hpos]
  have hs : ((n : ℝ) + 2) ^ (-σ) = ((n : ℝ) + 2) ^ (1 - σ) * ((n : ℝ) + 2)⁻¹ := by
    rw [show -σ = (1 - σ) - 1 by ring, Real.rpow_sub_one hy0.ne', div_eq_mul_inv]
  have hyp : 0 < ((n : ℝ) + 2) ^ (1 - σ) := Real.rpow_pos_of_pos hy0 _
  have := mul_le_mul_of_nonneg_left hb hyp.le
  unfold er
  rw [hm, hs]
  nlinarith
end Formalism.ZRN
