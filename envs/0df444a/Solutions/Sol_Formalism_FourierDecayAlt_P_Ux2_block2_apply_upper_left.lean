-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Ux2.block2_apply_upper_left
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T16:34:48.833838+00:00
-- url     : https://prove2.me/submissions/7bfe372b-c5d7-4030-8d81-f016e586e614

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
theorem _root_.solution (A : Matrix (Fin p) (Fin p) ℂ) (B : Matrix (Fin p) (Fin s) ℂ)
    (C : Matrix (Fin s) (Fin p) ℂ) (D : Matrix (Fin s) (Fin s) ℂ) (x y : Fin p) :
    blk2 A B C D (Fin.castAdd s x) (Fin.castAdd s y) = A x y := by simp [blk2]
end Formalism.FourierDecayAlt.P.Ux2
