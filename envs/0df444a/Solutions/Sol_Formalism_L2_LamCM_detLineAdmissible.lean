-- Prove2me | solution 1 for Formalism.L2.LamCM.detLineAdmissible
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T13:17:03.822943+00:00
-- url     : https://prove2.me/submissions/3684a989-46fc-42b2-9307-ea054d356062

import Definitions.Def_Formalism_LocalToGlobal_CMDeterminantIdeals_StatementA
import Definitions.Def_Formalism_LocalToGlobal_CMDeterminantIdeals_CMIdealValuations_ProdMulLeDetIdeal
import Theorems.Thm_Formalism_L2_LamCM_A2_det_re_pos
import Theorems.Thm_Formalism_L2_LamCM_A2_detSub_isFractional
import Theorems.Thm_Formalism_L2_LamCM_A2_detIdeal_ne_zero

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.L2 Formalism.L2.LamCM
open NumberField IsDedekindDomain
open scoped nonZeroDivisors ComplexOrder
open A2
namespace Formalism.L2.LamCM
theorem _root_.solution : DetGood := by
  intro K _ _ m L hL
  refine ⟨detSub_isFractional L hL.1, ?_⟩
  show L.detIdeal ≠ 0 ∧ ∀ σ, 0 < Real.sqrt (L.H σ).det.re
  exact ⟨detIdeal_ne_zero L hL, fun σ => Real.sqrt_pos.2 (det_re_pos (hL.2.2 σ))⟩
end Formalism.L2.LamCM
