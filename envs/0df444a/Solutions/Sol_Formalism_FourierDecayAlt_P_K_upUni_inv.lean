-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.K.upUni_inv
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T11:36:53.022842+00:00
-- url     : https://prove2.me/submissions/ac995d09-4e0a-4f3c-bad5-d193b1176e5c

import Definitions.Def_Formalism_HermitianCurvature_StatementK
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_RecText
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_AntidiagMulDiagonal
import Theorems.Thm_Formalism_FourierDecayAlt_P_K_diag_mul
import Theorems.Thm_Formalism_FourierDecayAlt_P_K_upUni_isUnit

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
theorem _root_.solution {a : Matrix (Fin n) (Fin n) K} (ha : IsUpUni a) : IsUpUni a⁻¹ := by
  haveI := Matrix.invertibleOfIsUnitDet a (upUni_isUnit ha)
  have hinv := Matrix.blockTriangular_inv_of_blockTriangular ha.1
  refine ⟨hinv, fun i => ?_⟩
  have h := diag_mul hinv ha.1 i
  rw [Matrix.nonsing_inv_mul _ (upUni_isUnit ha), ha.2, mul_one, Matrix.one_apply_eq] at h
  exact h.symm
end Formalism.FourierDecayAlt.P.K
