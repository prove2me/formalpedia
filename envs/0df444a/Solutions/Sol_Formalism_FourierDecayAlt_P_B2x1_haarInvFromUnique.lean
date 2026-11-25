-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.B2x1.haarInvFromUnique
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T16:37:42.752986+00:00
-- url     : https://prove2.me/submissions/34d12243-40a9-4f4c-96fe-8427fcb4c9c1

import Definitions.Def_Formalism_HermitianCurvature_WeylElementCommutesLevelOne
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_BlochKatoDuality
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ConjugationContinuousOnInvertible
import Theorems.Thm_UpperTheory_Reformulated_B_BlochKatoDuality_haarInvFromUnique


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
theorem _root_.solution : HaarInvFromUnique :=
  _root_.UpperTheory.Reformulated.B.BlochKatoDuality.haarInvFromUnique
end Formalism.FourierDecayAlt.P.B2x1
