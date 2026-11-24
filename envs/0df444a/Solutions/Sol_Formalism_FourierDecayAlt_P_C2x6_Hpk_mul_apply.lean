-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.C2x6.Hpk_mul_apply
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T15:55:15.353801+00:00
-- url     : https://prove2.me/submissions/845f6f84-0cfc-4e2c-aab9-827b9b4765a6

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_HermitianFormFlagVector
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_MajorantEstimate
import Theorems.Thm_Formalism_QuantumDeterminants_GBasic_Hpk_eq


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
open Formalism.FourierDecayAlt.P.C2x6
open C2x5
variable {k r : ℕ}
namespace Formalism.FourierDecayAlt.P.C2x6
theorem _root_.solution (M : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) (i j : Fin (2 * r + k + 1)) :
    (Hpk k r * M) i j = GBasic.sgn k r i * M (GBasic.sig k r i) j := by
  rw [Matrix.mul_apply]
  simp [GBasic.Hpk_eq]
end Formalism.FourierDecayAlt.P.C2x6
