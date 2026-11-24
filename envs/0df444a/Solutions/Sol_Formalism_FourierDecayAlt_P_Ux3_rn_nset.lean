-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Ux3.rn_nset
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T17:11:05.626243+00:00
-- url     : https://prove2.me/submissions/ee026135-4117-4c6e-a9f2-caa835fd2126

import Definitions.Def_Formalism_HermitianCurvature_StatementU
import Definitions.Def_Formalism_FormalDegreeBessel_FinalG
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_SymmetricScalarBlockMatrixMul
import Theorems.Thm_Formalism_FourierDecayAlt_P_Ux3_rn_eq
import Theorems.Thm_Formalism_FourierDecayAlt_P_Ux3_rn_unitary
import Theorems.Thm_Formalism_FourierDecayAlt_P_Ux3_uni_nset

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
theorem _root_.solution (x : RC k j ρ) : Rn k j ρ x ∈ Nset k (j + ρ) := by
  have h := rn_unitary x
  rw [rn_eq] at h ⊢
  exact uni_nset _ _ _ h
end Formalism.FourierDecayAlt.P.Ux3
