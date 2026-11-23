-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.K.upUni_mul
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T11:29:38.327312+00:00
-- url     : https://prove2.me/submissions/fe31e961-5fa0-414f-b647-0c7747f9dbe7

import Definitions.Def_Formalism_HermitianCurvature_StatementK
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_RecText
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_AntidiagMulDiagonal
import Theorems.Thm_Formalism_FourierDecayAlt_P_K_diag_mul

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
theorem _root_.solution {a b : Matrix (Fin n) (Fin n) K} (ha : IsUpUni a) (hb : IsUpUni b) :
    IsUpUni (a * b) := ⟨Matrix.BlockTriangular.mul ha.1 hb.1, fun i => by rw [diag_mul ha.1 hb.1, ha.2, hb.2, one_mul]⟩
end Formalism.FourierDecayAlt.P.K
