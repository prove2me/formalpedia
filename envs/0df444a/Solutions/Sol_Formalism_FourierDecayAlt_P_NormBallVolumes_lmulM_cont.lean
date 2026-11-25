-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.NormBallVolumes.lmulM_cont
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T16:40:51.480242+00:00
-- url     : https://prove2.me/submissions/ab2d87a6-5467-4ca5-8f44-95c8651b2f2a

import Definitions.Def_Formalism_HermitianCurvature_WeylElementCommutesLevelOne
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_BetaSesquilinearity
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_FrobeniusBoundOfMulNearOne
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_LiftingTheory
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_NormBallVolumes

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
theorem _root_.solution {k r : ℕ} (a : Mat k r) : Continuous (lmulM a : Mt k r → Mt k r) := by
  have hof : Continuous (fun x : Mt k r => (Matrix.of x : Mat k r)) := continuous_id
  exact (continuous_const (y := a)).matrix_mul hof
end Formalism.FourierDecayAlt.P.NormBallVolumes
