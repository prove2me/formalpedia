-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.C2x5.hermitian_form_flag_vector
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T16:37:46.820628+00:00
-- url     : https://prove2.me/submissions/876fd542-ab24-42d9-b156-e9193cc3ad44

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_StabilizerAntidiagonalExact
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_HermitianFormFlagVector
import Theorems.Thm_Formalism_FourierDecayAlt_P_C2x5_herm_e_alt

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Formalism.FourierDecayAlt Formalism.QuantumDeterminants
open scoped ComplexConjugate
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P
open Formalism.FourierDecayAlt.P.C2x5
variable {k r : ℕ}
namespace Formalism.FourierDecayAlt.P.C2x5
theorem _root_.solution {z : Fin (2 * r + k + 1) → ℂ} (hz : inWb k r z) (c : Fin (r + 1)) :
    herm (Hpk k r) (fvec k r z c) z = if c.val = r then herm (Hpk k r) z z else 0 := by
  unfold fvec
  split_ifs with h1 h2 h2
  · omega
  · exact herm_e_alt hz _ (Or.inl (by simp [eI, h1]))
  · rfl
  · omega
end Formalism.FourierDecayAlt.P.C2x5
