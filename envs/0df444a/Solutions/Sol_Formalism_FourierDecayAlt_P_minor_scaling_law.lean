-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.minor_scaling_law
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T16:50:49.043276+00:00
-- url     : https://prove2.me/submissions/66d2e89e-d542-4e86-ae0c-eeb86285d716

import Definitions.Def_Formalism_HermitianCurvature_StatementX
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ScalingExponentIdentities
import Theorems.Thm_Formalism_FourierDecayAlt_P_X_scaled_eq
import Theorems.Thm_Formalism_FourierDecayAlt_P_X_prod_pow_fin
import Theorems.Thm_Formalism_FourierDecayAlt_P_X_two_sum

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P
open Matrix
namespace Formalism.FourierDecayAlt.P
theorem _root_.solution : Formalism.FourierDecayAlt.X.MinorScale := by
  intro K _ n Z κ l hl
  rw [X.scaled_eq n Z κ l hl, Matrix.det_mul, Matrix.det_mul, Matrix.det_diagonal,
    X.prod_pow_fin, ← X.two_sum, pow_mul]
  ring
end Formalism.FourierDecayAlt.P
