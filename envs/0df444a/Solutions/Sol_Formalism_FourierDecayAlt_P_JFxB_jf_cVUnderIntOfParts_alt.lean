-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.JFxB.jf_cVUnderIntOfParts_alt
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T16:54:12.908712+00:00
-- url     : https://prove2.me/submissions/a7d03e2b-f05b-4648-89b7-6d3dc75af2b3

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CvRhoOfParts
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_RegularisedPairingViaPhase
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_JfCVUnderIntOfParts
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
namespace Formalism.FourierDecayAlt.P.JFxB
theorem _root_.solution : Formalism.FourierDecayAlt.JF.CVUnderIntOfParts := by
  intro hJ hW hR
  exact Formalism.FourierDecayAlt.P.JFxB.cvUnderInt_of hJ hW hR
end Formalism.FourierDecayAlt.P.JFxB
