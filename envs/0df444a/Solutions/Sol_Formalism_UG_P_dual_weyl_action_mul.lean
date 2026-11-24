-- Prove2me | solution 1 for Formalism.UG.P.dual_weyl_action_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T11:55:29.994129+00:00
-- url     : https://prove2.me/submissions/86c45926-c27f-48d5-b824-57e27e5fc8ae

import Definitions.Def_Formalism_SatakeDualWeyl_StatementW
import Definitions.Def_Formalism_GradedWeylDivisibility_DualWeylDominanceOf
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_DualWeylModuleStable
import Theorems.Thm_Formalism_UG_P_wact_rowAct_mul
import Theorems.Thm_Formalism_UG_P_wact_rowAct_one
import Theorems.Thm_Formalism_GradedWeylDivisibility_rowDivL_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.GradedWeylDivisibility.rowDivL_apply



set_option autoImplicit false
noncomputable section
open MvPolynomial
open Formalism Formalism.UG Formalism.UG.P
namespace Formalism.UG.P
theorem _root_.solution : Formalism.UG.DwActMul := by
  intro R _ r n g h
  refine ⟨?_, ?_⟩
  · simp only [Formalism.UG.dwAct]
    rw [mul_inv_rev, Units.val_mul, wact_rowAct_mul]
  · simp only [Formalism.UG.dwAct, inv_one, Units.val_one]
    exact wact_rowAct_one R r n
end Formalism.UG.P
