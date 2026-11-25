-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.matrix_coefficient_integrable_crude_all
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T17:33:18.173447+00:00
-- url     : https://prove2.me/submissions/c88204ed-7b85-4b60-8c32-bc1d4d53bd30

import Definitions.Def_Formalism_HermitianCurvature_WeylElementCommutesLevelOne
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_BetaSesquilinearity
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_FrobeniusBoundOfMulNearOne
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_LiftingTheory
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_NormBallVolumes
import Theorems.Thm_Formalism_FourierDecayAlt_P_NormBallVolumes_gnLower
import Theorems.Thm_Formalism_FourierDecayAlt_P_NormBallVolumes_volCrude
import Theorems.Thm_Formalism_FourierDecayAlt_P_NormBallVolumes_shellInt
import Theorems.Thm_Formalism_FourierDecayAlt_P_norm_power_integrable_crude_of_volume
import Theorems.Thm_Formalism_FourierDecayAlt_P_matrix_coefficient_bound_by_norm
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
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2 Formalism.FourierDecayAlt.P.NormBallVolumes
namespace Formalism.FourierDecayAlt.P
theorem _root_.solution : Formalism.FourierDecayAlt.B2.CCIntCrudeAll := by
  intro k r Wp Wq _ _ _ _ D A hA
  exact matrix_coefficient_bound_by_norm k r Wp Wq D A
    (norm_power_integrable_crude_of_volume shellInt gnLower volCrude k r D.μG A D.haarG hA)
end Formalism.FourierDecayAlt.P
