-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Ux2.lowK_unit
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T16:36:32.563423+00:00
-- url     : https://prove2.me/submissions/73440ca0-5918-44ac-9022-26b659ca0c9f

import Definitions.Def_Formalism_HermitianCurvature_StatementU
import Definitions.Def_Formalism_FormalDegreeBessel_FinalG
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_MulDiagOfTriangular
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_SymmetricScalarBlockMatrixTranspose
import Theorems.Thm_Formalism_FourierDecayAlt_P_Ux2_kL_lt

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Formalism.FourierDecayAlt Formalism.FourierDecayAlt.U Formalism.REAL Formalism.QuantumDeterminants
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.Ux2
variable {p : ℕ}
namespace Formalism.FourierDecayAlt.P.Ux2
theorem _root_.solution {L : Matrix (Fin p) (Fin p) ℂ} (h : uniK (kL p) L) : IsUnit L.det := by
  rw [Matrix.det_of_isLowerTriangular L (fun i j hij => h.2 i j (kL_lt.mpr (OrderDual.toDual_lt_toDual.mp hij)))]
  simp [h.1]
end Formalism.FourierDecayAlt.P.Ux2
