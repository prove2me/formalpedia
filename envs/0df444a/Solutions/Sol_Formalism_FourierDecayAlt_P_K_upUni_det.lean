-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.K.upUni_det
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T11:29:38.207539+00:00
-- url     : https://prove2.me/submissions/9891fa9e-dcb4-4e3e-80b8-352712e0e516

import Definitions.Def_Formalism_HermitianCurvature_StatementK
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_RecText
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_AntidiagMulDiagonal

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
theorem _root_.solution {a : Matrix (Fin n) (Fin n) K} (ha : IsUpUni a) : a.det = 1 := by
  rw [Matrix.det_of_upperTriangular ha.1]
  simp [ha.2]
end Formalism.FourierDecayAlt.P.K
