-- Prove2me | solution 1 for Formalism.LatticeIndexTer.le_ph_sub
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T10:35:30.825478+00:00
-- url     : https://prove2.me/submissions/5cb27fe8-3891-4a00-b1fe-d73a01ecb4e4

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
theorem _root_.solution {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    (b - a) * Real.log a ≤ ph b - ph a := by
  have hb : 0 < b := lt_of_lt_of_le ha hab
  have h1 := Real.log_le_sub_one_of_pos (div_pos ha hb)
  rw [Real.log_div ha.ne' hb.ne'] at h1
  have h2 := mul_le_mul_of_nonneg_left h1 hb.le
  have h3 : b * (a / b - 1) = a - b := by field_simp <;> ring
  rw [h3] at h2
  unfold ph
  linarith
end Formalism.LatticeIndexTer
