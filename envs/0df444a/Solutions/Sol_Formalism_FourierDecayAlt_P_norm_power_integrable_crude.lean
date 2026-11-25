-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.norm_power_integrable_crude
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T16:50:53.137201+00:00
-- url     : https://prove2.me/submissions/936d1b75-2ccd-448c-8336-95f247eb93ec

import Definitions.Def_Formalism_HermitianCurvature_WeylElementCommutesLevelOne
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_BetaSesquilinearity
import Definitions.Def_Formalism_RealPlaceAnalysis_FinalF
import Definitions.Def_Formalism_FormalDegreeBessel_FinalG
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_LiftErrorLocal
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_HaarUniquenessConjugation
import Theorems.Thm_Formalism_FourierDecayAlt_P_HaarUniquenessConjugation_shell_int
import Theorems.Thm_Formalism_FourierDecayAlt_P_HaarUniquenessConjugation_gN_meas
import Theorems.Thm_Formalism_FourierDecayAlt_P_HaarUniquenessConjugation_ae_mem
import Theorems.Thm_Formalism_FourierDecayAlt_P_HaarUniquenessConjugation_gnLower
import Theorems.Thm_Formalism_FourierDecayAlt_P_norm_ball_volume_crude
import Theorems.Thm_UpperTheory_Reformulated_B_LiftErrorLocal_shell_int


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix MeasureTheory Filter Topology
open scoped ComplexConjugate ENNReal NNReal
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2
namespace Formalism.FourierDecayAlt.P
theorem _root_.solution : Formalism.FourierDecayAlt.B2.GNIntCrude := by
  intro k r μG A hμ hA
  obtain ⟨C, hC⟩ := norm_ball_volume_crude k r μG hμ
  refine HaarUniquenessConjugation.shell_int (Mt k r) μG (fun g => gN (Matrix.of g)) C _ A (HaarUniquenessConjugation.gN_meas k r) ?_ (by positivity) hC hA
  filter_upwards [HaarUniquenessConjugation.ae_mem hμ] with g hg using HaarUniquenessConjugation.gnLower k r _ hg
end Formalism.FourierDecayAlt.P
