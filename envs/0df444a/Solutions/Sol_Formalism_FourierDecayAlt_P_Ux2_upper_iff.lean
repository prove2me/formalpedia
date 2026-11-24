-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Ux2.upper_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T15:15:52.441512+00:00
-- url     : https://prove2.me/submissions/77a072ab-247e-4e75-b13f-93159a92b0b7

import Definitions.Def_Formalism_HermitianCurvature_StatementU
import Definitions.Def_Formalism_FormalDegreeBessel_FinalG
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_MulDiagOfTriangular
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_SymmetricScalarBlockMatrixTranspose
import Theorems.Thm_Formalism_FourierDecayAlt_P_Ux2_kU_lt

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
theorem _root_.solution (u : Matrix (Fin p) (Fin p) ℂ) : G.IsUpperUni u ↔ uniK (kU p) u := by
  simp [G.IsUpperUni, uniK, kU_lt]
end Formalism.FourierDecayAlt.P.Ux2
