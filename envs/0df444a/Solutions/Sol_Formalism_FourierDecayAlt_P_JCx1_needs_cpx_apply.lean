-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.JCx1.needs.cpx_apply
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T18:05:53.752143+00:00
-- url     : https://prove2.me/submissions/fa6f3b39-349e-4a24-bd13-c07c5350e46e

import Definitions.Def_Formalism_HermitianCurvature_StatementJC
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_FrameIntegralJacobian
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_BlockEstimatesSumForm
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_BigCellZetaMinors
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_RegularisedPairingViaPhase
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LevelSizesJointMean
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_TheoremPIntegralOfPlaces

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.FourierDecayAlt
open Formalism.FourierDecayAlt
open Formalism.FourierDecayAlt Filter Topology MeasureTheory NumberField
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.JCx1 Formalism.FourierDecayAlt.P.JCx1.needs
noncomputable section
open scoped Classical
variable (E : Type) [Field E] [NumberField E] [IsCMField E]
namespace Formalism.FourierDecayAlt.P.JCx1.needs
theorem _root_.solution (c : J.CV E) (w : {w : InfinitePlace E // w.IsComplex}) : cpx E c w = c w.1 := by
  rfl
end Formalism.FourierDecayAlt.P.JCx1.needs
