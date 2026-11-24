-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Ux2.supS_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T15:02:35.410711+00:00
-- url     : https://prove2.me/submissions/107d8bd6-dc7b-4e0b-a9e8-da3385728deb

import Definitions.Def_Formalism_HermitianCurvature_StatementU
import Definitions.Def_Formalism_FormalDegreeBessel_FinalG
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_MulDiagOfTriangular
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_SymmetricScalarBlockMatrixTranspose

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
variable {p s : ℕ}
namespace Formalism.FourierDecayAlt.P.Ux2
theorem _root_.solution (M : Matrix (Fin p) (Fin p) ℂ) : supS M = subS Mᵀ := by
  simp [subS, supS, transpose_apply]
end Formalism.FourierDecayAlt.P.Ux2
