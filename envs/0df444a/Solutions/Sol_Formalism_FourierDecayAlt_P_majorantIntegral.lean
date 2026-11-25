-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.majorantIntegral
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T16:46:30.526594+00:00
-- url     : https://prove2.me/submissions/e7ca9e96-170c-4ef6-a09d-624cdf1d0d44

import Definitions.Def_Formalism_HermitianCurvature_LatticeHerglotzBound
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_MajorantIntegrals
import Theorems.Thm_Formalism_FourierDecayAlt_P_MajorantIntegrals_majIntegral_ok

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
theorem _root_.solution : Formalism.FourierDecayAlt.crystallineComparison.MajIntegral := Formalism.FourierDecayAlt.P.MajorantIntegrals.majIntegral_ok
end Formalism.FourierDecayAlt.P
