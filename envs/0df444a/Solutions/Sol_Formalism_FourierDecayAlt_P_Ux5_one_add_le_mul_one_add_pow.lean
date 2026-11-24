-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Ux5.one_add_le_mul_one_add_pow
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T16:32:49.966953+00:00
-- url     : https://prove2.me/submissions/b6becd2c-48ed-4d79-bdc7-26cdaca609b9

import Definitions.Def_Formalism_HermitianCurvature_StatementU
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_GBasic
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_DetNormLe
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_Block3MulBlocks

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Formalism.FourierDecayAlt Formalism.FourierDecayAlt.U Formalism.QuantumDeterminants
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.Ux5
namespace Formalism.FourierDecayAlt.P.Ux5
theorem _root_.solution {x c m : ℝ} {k : ℕ} (hc : 0 ≤ c) (hm : 0 ≤ m) (h : x ≤ c * m ^ k) :
    1 + x ≤ (1 + c) * (1 + m) ^ k := by
  have h1 : m ^ k ≤ (1 + m) ^ k := pow_le_pow_left₀ hm (by linarith) k
  have h2 : 1 ≤ (1 + m) ^ k := one_le_pow₀ (by linarith)
  nlinarith [mul_le_mul_of_nonneg_left h1 hc]
end Formalism.FourierDecayAlt.P.Ux5
