-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.majorantIntegralProd
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T16:46:36.69238+00:00
-- url     : https://prove2.me/submissions/da7ce19c-0304-40b0-a06b-5504b6a9bff3

import Definitions.Def_Formalism_HermitianCurvature_LatticeHerglotzBound
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_MajorantIntegrals
import Theorems.Thm_Formalism_FourierDecayAlt_P_MajorantIntegrals_majIntegralProd_ok

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Set
noncomputable section
namespace Formalism.FourierDecayAlt.P
theorem _root_.solution : Formalism.FourierDecayAlt.crystallineComparison.MajIntegralProd :=
  Formalism.FourierDecayAlt.P.MajorantIntegrals.majIntegralProd_ok
end Formalism.FourierDecayAlt.P
