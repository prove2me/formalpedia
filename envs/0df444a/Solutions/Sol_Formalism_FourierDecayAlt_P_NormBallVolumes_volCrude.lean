-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.NormBallVolumes.volCrude
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T17:07:05.925896+00:00
-- url     : https://prove2.me/submissions/3b45fafa-890e-446a-957a-81eb5b652c3d

import Definitions.Def_Formalism_HermitianCurvature_WeylElementCommutesLevelOne
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_BetaSesquilinearity
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_FrobeniusBoundOfMulNearOne
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_LiftingTheory
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_NormBallVolumes
import Theorems.Thm_UpperTheory_Reformulated_B_LiftingTheory_volCrude


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix MeasureTheory Filter Topology Metric
open scoped ComplexConjugate ENNReal NNReal
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.NormBallVolumes
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2
namespace Formalism.FourierDecayAlt.P.NormBallVolumes
theorem _root_.solution : VolCrude :=
  _root_.UpperTheory.Reformulated.B.LiftingTheory.volCrude
end Formalism.FourierDecayAlt.P.NormBallVolumes
