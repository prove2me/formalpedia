-- Prove2me | solution 1 for Formalism.UG.P.standard_action_mul_holds
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T05:32:16.094866+00:00
-- url     : https://prove2.me/submissions/75fa23a4-4f3b-481a-bc71-454b2686f5ed

import Definitions.Def_Formalism_SatakeDualWeyl_Statement
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_Actions

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
theorem _root_.solution : Formalism.UG.StdActMul := by
  intro O _ n _ _ g h
  refine ⟨?_, ?_⟩
  · unfold Formalism.UG.stdAct
    rw [Units.val_mul, Matrix.mulVecLin_mul]
  · unfold Formalism.UG.stdAct
    rw [Units.val_one, Matrix.mulVecLin_one]
end Formalism.UG.P
