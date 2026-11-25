-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.big_cell_bijection
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T02:37:53.394421+00:00
-- url     : https://prove2.me/submissions/17790a42-bbae-4ef0-a256-da18732828f7

import Definitions.Def_Formalism_HermitianCurvature_StatementU
import Definitions.Def_Formalism_FormalDegreeBessel_FinalG
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_SymmetricScalarBlockMatrixMul
import Theorems.Thm_Formalism_FourierDecayAlt_P_Ux3_bigCellBij

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
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P
namespace Formalism.FourierDecayAlt.P
theorem _root_.solution : Formalism.FourierDecayAlt.U.BigCellBij := Ux3.bigCellBij
end Formalism.FourierDecayAlt.P
