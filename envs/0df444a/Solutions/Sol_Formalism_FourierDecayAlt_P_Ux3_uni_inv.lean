-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Ux3.uni_inv
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T16:00:03.081893+00:00
-- url     : https://prove2.me/submissions/e2a7de98-af10-4746-b157-281c647f10cf

import Definitions.Def_Formalism_HermitianCurvature_StatementU
import Definitions.Def_Formalism_FormalDegreeBessel_FinalG
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_SymmetricScalarBlockMatrixMul
import Theorems.Thm_Formalism_FourierDecayAlt_P_Ux3_uni_mul_inv

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.U
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.Ux3
variable {k j ρ : ℕ}
namespace Formalism.FourierDecayAlt.P.Ux3
theorem _root_.solution (a : Matrix (Fin j) (Fin (2 * ρ + k + 1)) ℂ) (b : Matrix (Fin j) (Fin j) ℂ)
    (c : Matrix (Fin (2 * ρ + k + 1)) (Fin j) ℂ) :
    (blk3 1 a b 0 1 c 0 0 1)⁻¹ = blk3 1 (-a) (a * c - b) 0 1 (-c) 0 0 1 := Matrix.inv_eq_right_inv (uni_mul_inv a b c)
end Formalism.FourierDecayAlt.P.Ux3
