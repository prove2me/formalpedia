-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.latticeSummable_statement
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T16:46:36.821873+00:00
-- url     : https://prove2.me/submissions/85dfc532-c18f-4e60-9a4a-ceb0b08bde63

import Definitions.Def_Formalism_HermitianCurvature_LatticeHerglotzBound
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_MajorantIntegrals
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LatticeSummability
import Theorems.Thm_Formalism_FourierDecayAlt_P_LatticeSummability_latticeSummable

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Set Finset Function
noncomputable section
namespace Formalism.FourierDecayAlt.P
theorem _root_.solution : Formalism.FourierDecayAlt.crystallineComparison.LatticeSummable := LatticeSummability.latticeSummable
end Formalism.FourierDecayAlt.P
