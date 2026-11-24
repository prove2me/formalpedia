-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Ux3.eC_symm_natAdd
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T16:29:32.020697+00:00
-- url     : https://prove2.me/submissions/a005ffb6-44d6-483e-a49f-23b14732fb73

import Definitions.Def_Formalism_HermitianCurvature_StatementU
import Definitions.Def_Formalism_FormalDegreeBessel_FinalG
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_SymmetricScalarBlockMatrixMul
import Theorems.Thm_Formalism_FourierDecayAlt_P_Ux3_column_index_second_val

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
theorem _root_.solution {l : ℕ} (h : j + l ≤ j + ρ + 1) (hl : l ≤ ρ + 1) (c : Fin l) :
    (eC j ρ).symm (Fin.castLE h (Fin.natAdd j c)) = Sum.inr (Fin.castLE hl c) := by
  rw [Equiv.symm_apply_eq]
  apply Fin.ext
  simp [column_index_second_val]
end Formalism.FourierDecayAlt.P.Ux3
