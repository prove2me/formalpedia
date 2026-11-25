-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.density_chain
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T16:45:22.534443+00:00
-- url     : https://prove2.me/submissions/fe56f5d6-b7f7-4ad0-aae3-56caedafc200

import Definitions.Def_Formalism_HermitianCurvature_StatementTC
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_DensitySumsAndDomination
import Theorems.Thm_Formalism_FourierDecayAlt_P_DensitySumsAndDomination_densChain

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
theorem _root_.solution : Formalism.FourierDecayAlt.TC.DensChain := DensitySumsAndDomination.densChain
end Formalism.FourierDecayAlt.P
