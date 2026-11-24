-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Ux2.uniK_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T16:34:55.495307+00:00
-- url     : https://prove2.me/submissions/ca1e25b1-6639-4c66-abc4-2ced25e03a5e

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
variable {p : ℕ}
namespace Formalism.FourierDecayAlt.P.Ux2
theorem _root_.solution (κ : Fin p → ℤ) : uniK κ 1 :=
  ⟨fun i => Matrix.one_apply_eq i, fun a b hab => Matrix.one_apply_ne (fun h => by subst h; exact lt_irrefl _ hab)⟩
end Formalism.FourierDecayAlt.P.Ux2
