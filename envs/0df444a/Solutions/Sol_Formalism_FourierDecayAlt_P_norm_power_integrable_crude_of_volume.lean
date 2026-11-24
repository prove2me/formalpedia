-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.norm_power_integrable_crude_of_volume
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T16:44:08.438066+00:00
-- url     : https://prove2.me/submissions/584ed136-02a6-4cdf-a186-4faeb4b76fc6

import Definitions.Def_Formalism_HermitianCurvature_WeylElementCommutesLevelOne
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_BetaSesquilinearity
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_FrobeniusBoundOfMulNearOne
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_LiftingTheory
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_NormBallVolumes
import Theorems.Thm_Formalism_FourierDecayAlt_P_NormBallVolumes_gN_meas
import Theorems.Thm_Formalism_FourierDecayAlt_P_NormBallVolumes_ae_mem

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
theorem _root_.solution : Formalism.FourierDecayAlt.B2.GNIntCrudeFromVol := by
  intro hS hL hV k r μG A hμ hA
  obtain ⟨C, hC⟩ := hV k r μG hμ
  refine hS (Mt k r) μG (fun g => gN (Matrix.of g)) C _ A (gN_meas k r) ?_ (by positivity) hC hA
  filter_upwards [ae_mem hμ] with g hg using hL k r _ hg
end Formalism.FourierDecayAlt.P
