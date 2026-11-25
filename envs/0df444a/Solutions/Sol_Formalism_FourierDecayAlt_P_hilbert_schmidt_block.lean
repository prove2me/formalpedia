-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.hilbert_schmidt_block
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T17:05:38.145286+00:00
-- url     : https://prove2.me/submissions/2771e8b8-1776-4f41-93de-81b938eea608

import Definitions.Def_Formalism_HermitianCurvature_WeylElementCommutesLevelOne
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_BetaSesquilinearity
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_HermitianFormFactor
import Theorems.Thm_Formalism_FourierDecayAlt_P_HermitianFormFactor_hsblock

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
theorem _root_.solution : Formalism.FourierDecayAlt.B2.HSBlock := by
  exact HermitianFormFactor.hsblock
end Formalism.FourierDecayAlt.P
