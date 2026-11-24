-- Prove2me | solution 1 for Formalism.UG.P.tensor_action_mul_holds
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T11:39:43.724266+00:00
-- url     : https://prove2.me/submissions/8382df9d-49d4-42e9-b259-25569179979c

import Definitions.Def_Formalism_SatakeDualWeyl_Statement
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_Actions
import Theorems.Thm_Formalism_UG_P_standard_action_mul_holds

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
theorem _root_.solution : Formalism.UG.TensActMul := by
  intro O _ n _ _ k g h
  refine ⟨?_, ?_⟩
  · unfold Formalism.UG.tensAct
    rw [← PiTensorProduct.map_comp]
    congr 1
    funext i
    exact (standard_action_mul_holds O n g h).1
  · unfold Formalism.UG.tensAct
    have : (fun _ : Fin k => Formalism.UG.stdAct O n 1) = fun _ => LinearMap.id :=
      funext fun _ => (standard_action_mul_holds O n 1 1).2
    rw [this, PiTensorProduct.map_id]
end Formalism.UG.P
