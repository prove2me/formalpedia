-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Ux3.herm_eq_zhat
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T16:28:49.734929+00:00
-- url     : https://prove2.me/submissions/10cdd79d-0007-4d6d-92e4-88a9ea7c03b0

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
theorem _root_.solution (r : ℕ) (v : Fin (2 * r + k + 1) → ℂ) :
    herm (Hpk k r) v v = Zhat k r v v 1 (Fin.last r) (Fin.last r) := by
  simp [Zhat, fvec]
end Formalism.FourierDecayAlt.P.Ux3
