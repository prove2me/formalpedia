-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.jf_cVUnderInt_of
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T16:46:22.045094+00:00
-- url     : https://prove2.me/submissions/d755ab39-7dd9-4e00-9bcf-73902fb3ee99

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CvRhoOfParts
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_RegularisedPairingViaPhase
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_JfCVUnderIntOfParts
import Theorems.Thm_Formalism_FourierDecayAlt_P_JFxB_cvWordSum
import Theorems.Thm_Formalism_FourierDecayAlt_P_JFxB_cvUnderInt_of

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix MeasureTheory Filter Topology
open scoped ContDiff
noncomputable section
namespace Formalism.FourierDecayAlt.P
theorem _root_.solution : Formalism.FourierDecayAlt.JF.JWords → Formalism.FourierDecayAlt.JF.RwRho → Formalism.FourierDecayAlt.JF.CVUnderInt :=
  fun hJ hR => Formalism.FourierDecayAlt.P.JFxB.cvUnderInt_of hJ Formalism.FourierDecayAlt.P.JFxB.cvWordSum hR
end Formalism.FourierDecayAlt.P
