-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.norm_ball_volume_exact
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T16:46:37.052656+00:00
-- url     : https://prove2.me/submissions/fc48f38b-2c79-44b2-b24c-2fdcf05998de

import Definitions.Def_Formalism_HermitianCurvature_WeylElementCommutesLevelOne
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_BetaSesquilinearity
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_HermitianFormFactor
import Theorems.Thm_Formalism_FourierDecayAlt_P_HermitianFormFactor_volExact

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix MeasureTheory Filter Topology
open scoped ComplexConjugate ENNReal NNReal ComplexOrder
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P
namespace Formalism.FourierDecayAlt.P
theorem _root_.solution : Formalism.FourierDecayAlt.B2.VolExact := by
  exact HermitianFormFactor.volExact
end Formalism.FourierDecayAlt.P
