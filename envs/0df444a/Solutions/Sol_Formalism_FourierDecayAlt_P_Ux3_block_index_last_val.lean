-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Ux3.block_index_last_val
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T14:53:50.710116+00:00
-- url     : https://prove2.me/submissions/18f98f46-0cd3-4c01-b402-a95069016237

import Definitions.Def_Formalism_HermitianCurvature_StatementU
import Definitions.Def_Formalism_FormalDegreeBessel_FinalG
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_SymmetricScalarBlockMatrixMul

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
theorem _root_.solution (a : Fin j) : (eB k j ρ (Sum.inr a)).val = j + (2 * ρ + k + 1) + a.val := by
  simp [eB]
end Formalism.FourierDecayAlt.P.Ux3
