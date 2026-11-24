-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Ux2.kL_lt
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T14:51:16.362312+00:00
-- url     : https://prove2.me/submissions/e525df33-b682-465e-a653-29ebae66d36b

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
theorem _root_.solution {a b : Fin p} : kL p a < kL p b ↔ a < b := by
  simp only [kL, Nat.cast_lt]; exact Fin.lt_def.symm
end Formalism.FourierDecayAlt.P.Ux2
