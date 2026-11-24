-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.norm_power_integrable_sharp_of_volume
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T16:44:09.185093+00:00
-- url     : https://prove2.me/submissions/8c52f302-a54a-481a-9629-8f020339b3d2

import Definitions.Def_Formalism_HermitianCurvature_WeylElementCommutesLevelOne
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_BetaSesquilinearity
import Definitions.Def_Formalism_RealPlaceAnalysis_FinalF
import Definitions.Def_Formalism_FormalDegreeBessel_FinalG
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_LiftErrorLocal
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_HaarUniquenessConjugation
import Theorems.Thm_Formalism_FourierDecayAlt_P_HaarUniquenessConjugation_gN_meas
import Theorems.Thm_Formalism_FourierDecayAlt_P_HaarUniquenessConjugation_ae_mem

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
theorem _root_.solution : Formalism.FourierDecayAlt.B2.GNIntSharpFromVol := by
  intro hS hL hV k r μG A hμ hA
  obtain ⟨C, hC⟩ := hV k r μG hμ
  refine hS (Mt k r) μG (fun g => gN (Matrix.of g)) C (2 * ((k : ℝ) + r) * ((r : ℝ) + 1)) A (HaarUniquenessConjugation.gN_meas k r) ?_
    (by positivity) hC ?_
  · filter_upwards [HaarUniquenessConjugation.ae_mem hμ] with g hg using hL k r _ hg
  · unfold AB at hA; linarith
end Formalism.FourierDecayAlt.P
