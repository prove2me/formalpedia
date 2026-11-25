-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.domination_after_of_local
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T16:37:37.666725+00:00
-- url     : https://prove2.me/submissions/1bf19bef-7c12-4d23-a446-ba9ec0d61c16

import Definitions.Def_Formalism_HermitianCurvature_StatementTC
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_DensitySumsAndDomination
import Theorems.Thm_Formalism_FourierDecayAlt_P_DensitySumsAndDomination_domAfterOfLocal

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset Filter Topology Formalism.FourierDecayAlt Formalism.FourierDecayAlt.TC
open scoped ComplexInnerProductSpace ComplexOrder ComplexConjugate
noncomputable section
open Classical
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P
namespace Formalism.FourierDecayAlt.P
theorem _root_.solution : Formalism.FourierDecayAlt.TC.DomAfterOfLocal := DensitySumsAndDomination.domAfterOfLocal
end Formalism.FourierDecayAlt.P
