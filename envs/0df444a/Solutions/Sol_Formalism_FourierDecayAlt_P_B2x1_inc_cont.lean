-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.B2x1.inc_cont
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T16:01:23.424105+00:00
-- url     : https://prove2.me/submissions/0e0cb97c-224d-4c6e-ab9b-db50df8b1b39

import Definitions.Def_Formalism_HermitianCurvature_WeylElementCommutesLevelOne
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_BlochKatoDuality
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ConjugationContinuousOnInvertible

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix MeasureTheory Filter Topology
open scoped ENNReal NNReal
open Formalism.FourierDecayAlt.B2 Formalism.FourierDecayAlt.B Formalism.QuantumDeterminants Formalism.REAL
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.B2x1
variable {k r : ℕ}
variable {U : Set (Mat k r)} {hU : IsClosedSubgroup U}
namespace Formalism.FourierDecayAlt.P.B2x1
theorem _root_.solution : Continuous (inc : Gp U hU → Mt k r) := continuous_subtype_val
end Formalism.FourierDecayAlt.P.B2x1
