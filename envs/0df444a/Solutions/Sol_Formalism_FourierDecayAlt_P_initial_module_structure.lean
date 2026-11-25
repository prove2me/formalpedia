-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.initial_module_structure
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T00:47:10.914565+00:00
-- url     : https://prove2.me/submissions/010a812f-f3eb-4d2c-83f1-1512e7a6f764

import Definitions.Def_Formalism_HermitianCurvature_StatementWd
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_KroneckerEmbedMulApply
import Theorems.Thm_Formalism_FourierDecayAlt_P_Wd2_rtt_lift0
import Theorems.Thm_Formalism_FourierDecayAlt_P_Wd2_det_lift0
import Theorems.Thm_P2M_Formalism_FourierDecayAlt_P_Wd2_det_lift0__294f3c3e11fc
import Theorems.Thm_Formalism_FourierDecayAlt_P_Wd2_liftMatrix_conjTranspose
import Theorems.Thm_Formalism_FourierDecayAlt_P_Wd2_d0_one

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P
open Matrix Formalism.YangianSpanCharacter.T Formalism.FourierDecayAlt.W Formalism.FourierDecayAlt.Wd
namespace Formalism.FourierDecayAlt.P
theorem _root_.solution : Formalism.FourierDecayAlt.Wd.StartModule := by
  intro K A S _ _ _ _ _ _ _ _ QQ q hS
  refine ⟨star_one _, fun Y _ hY => ?_, fun Y _ Y' _ => ?_, fun Y _ _ => ?_, hS.q_real⟩
  · rw [Formalism.FourierDecayAlt.P.Wd2.d0_one, one_mul, Formalism.FourierDecayAlt.P.Wd2.liftMatrix_conjTranspose, hS.herm Y hY]
  · exact Formalism.FourierDecayAlt.P.Wd2.rtt_lift0 (QQ Y') (QQ Y) (Y' - Y) (hS.rtt Y Y')
  · exact ⟨Formalism.FourierDecayAlt.P.Wd2.det_lift0 (QQ Y) (QQ (Y + 1)) (q Y) (hS.det Y).1,
      Formalism.FourierDecayAlt.P.Wd2.det_lift0' (QQ Y) (QQ (Y + 1)) (q Y) (hS.det Y).2⟩
end Formalism.FourierDecayAlt.P
