-- Prove2me | solution 1 for Formalism.LatticeIndexTer.ph_ge_neg_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T10:35:33.907575+00:00
-- url     : https://prove2.me/submissions/e10f4bb8-0768-4721-8c89-d90f15f2662e

import Definitions.Def_Formalism_LogFactorialIndices_StatementSize
import Definitions.Def_Formalism_LogFactorialIndices_SignedSubspaceIndex_SumInterlacedBoundFails

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.LatticeIndexTer
open Finset
namespace Formalism.LatticeIndexTer
theorem _root_.solution {x : ℝ} (hx : 0 ≤ x) : -1 ≤ ph x := by
  rcases hx.eq_or_lt with rfl | hx'
  · simp [ph]
  · have h1 := Real.log_le_sub_one_of_pos (inv_pos.mpr hx')
    rw [Real.log_inv] at h1
    have h2 : x * x⁻¹ = 1 := mul_inv_cancel₀ hx'.ne'
    have h3 := mul_le_mul_of_nonneg_left h1 hx
    rw [mul_sub, h2, mul_one, mul_neg] at h3
    unfold ph
    linarith
end Formalism.LatticeIndexTer
