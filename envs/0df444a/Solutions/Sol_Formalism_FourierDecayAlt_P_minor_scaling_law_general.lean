-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.minor_scaling_law_general
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T16:46:02.765701+00:00
-- url     : https://prove2.me/submissions/264709de-e2e3-480f-927f-3a5beda7f84f

import Definitions.Def_Formalism_HermitianCurvature_StatementX
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_MinorScalingLawGeneral
import Theorems.Thm_Formalism_FourierDecayAlt_P_XGen_scaled_eq

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
theorem _root_.solution : Formalism.FourierDecayAlt.X.MinorScaleGen := by
  intro K _ n Z α β l hl
  rw [XGen.scaled_eq n Z α β l hl, Matrix.det_mul, Matrix.det_mul, Matrix.det_diagonal,
    Matrix.det_diagonal, Finset.prod_mul_distrib]
  ring
end Formalism.FourierDecayAlt.P
