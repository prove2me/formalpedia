-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.K.upUni_isUnit
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T11:34:29.402345+00:00
-- url     : https://prove2.me/submissions/1b44bdb2-becf-418e-b5ca-b4d0e8dcbfd2

import Definitions.Def_Formalism_HermitianCurvature_StatementK
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_RecText
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_AntidiagMulDiagonal
import Theorems.Thm_Formalism_FourierDecayAlt_P_K_upUni_det

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.K
open Matrix Finset Real Formalism.FourierDecayAlt.K
variable {K : Type} [Field K] {n : ℕ}
namespace Formalism.FourierDecayAlt.P.K
theorem _root_.solution {a : Matrix (Fin n) (Fin n) K} (ha : IsUpUni a) : IsUnit a.det := by
  rw [upUni_det ha]
  exact isUnit_one
end Formalism.FourierDecayAlt.P.K
