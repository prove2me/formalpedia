-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Ux2.eB_lr
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T14:57:10.287816+00:00
-- url     : https://prove2.me/submissions/05d6b7e0-380f-4a03-a7e8-39ce735deafd

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
variable {k j ρ : ℕ}
namespace Formalism.FourierDecayAlt.P.Ux2
theorem _root_.solution (v : Fin (2 * ρ + k + 1)) : (eB k j ρ (Sum.inl (Sum.inr v))).val = j + v.val := by simp [eB]
end Formalism.FourierDecayAlt.P.Ux2
