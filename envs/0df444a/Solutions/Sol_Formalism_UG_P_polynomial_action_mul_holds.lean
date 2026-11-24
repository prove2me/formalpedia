-- Prove2me | solution 1 for Formalism.UG.P.polynomial_action_mul_holds
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T11:50:55.475174+00:00
-- url     : https://prove2.me/submissions/04ad674c-a513-474a-986d-2689f77e8707

import Definitions.Def_Formalism_SatakeDualWeyl_Statement
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_Actions
import Theorems.Thm_Formalism_UG_P_linSubst_comp
import Theorems.Thm_Formalism_UG_P_linSubst_one

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.UG Formalism.UG.P
open Matrix MvPolynomial
namespace Formalism.UG.P
theorem _root_.solution : Formalism.UG.PolyActMul := by
  intro O _ n _ _ g h
  refine ⟨?_, ?_⟩
  · unfold Formalism.UG.polyAct
    rw [linSubst_comp, _root_.mul_inv_rev, Units.val_mul]
  · unfold Formalism.UG.polyAct
    rw [inv_one, Units.val_one, linSubst_one]
end Formalism.UG.P
