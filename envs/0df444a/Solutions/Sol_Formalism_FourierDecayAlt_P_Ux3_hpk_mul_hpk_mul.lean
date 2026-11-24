-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Ux3.hpk_mul_hpk_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T16:49:28.015397+00:00
-- url     : https://prove2.me/submissions/71a39015-c02a-41e6-9266-3f77de4aa9a5

import Definitions.Def_Formalism_HermitianCurvature_StatementU
import Definitions.Def_Formalism_FormalDegreeBessel_FinalG
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_SymmetricScalarBlockMatrixMul
import Theorems.Thm_Formalism_FourierDecayAlt_P_Ux3_hpk_sq
import Theorems.Thm_Formalism_QuantumDeterminants_WeylGroupFacts_hpk_sq


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
theorem _root_.solution {m : Type*} (k r : ℕ) (X : Matrix (Fin (2 * r + k + 1)) m ℂ) : Hpk k r * (Hpk k r * X) = X := by
  rw [← Matrix.mul_assoc, hpk_sq, Matrix.one_mul]
end Formalism.FourierDecayAlt.P.Ux3
