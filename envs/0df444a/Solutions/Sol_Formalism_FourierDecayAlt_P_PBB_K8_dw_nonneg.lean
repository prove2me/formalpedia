-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.PBB.K8.dw_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T17:08:33.028823+00:00
-- url     : https://prove2.me/submissions/7a2cd4fd-98e6-42ba-9c9c-38a81f82d8a1

import Definitions.Def_Formalism_HermitianCurvature_StatementKB
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_TheoremPIntegralOfPlaces
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_GramLocTendsto

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Filter Topology Real NumberField
open scoped FourierTransform RealInnerProductSpace ComplexConjugate
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.PBB Formalism.FourierDecayAlt.P.PBB.K8
noncomputable section
namespace Formalism.FourierDecayAlt.P.PBB.K8
theorem _root_.solution (c : ℂ) : 0 ≤ dw c := by unfold dw; positivity
end Formalism.FourierDecayAlt.P.PBB.K8
