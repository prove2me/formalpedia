-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.C2x5.hzz_ne
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T15:56:26.827893+00:00
-- url     : https://prove2.me/submissions/3e610f1f-b4d2-44cf-9ad0-281f96a07027

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_StabilizerAntidiagonalExact
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_HermitianFormFlagVector
import Theorems.Thm_Formalism_FourierDecayAlt_P_C2x5_hzz_real

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
theorem _root_.solution {z : Fin (2 * r + k + 1) → ℂ} (hz : 0 < Tz k r z) : herm (Hpk k r) z z ≠ 0 := by
  rw [hzz_real]; exact_mod_cast (neg_ne_zero.mpr hz.ne')
end Formalism.FourierDecayAlt.P.C2x5
