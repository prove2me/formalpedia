-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.haar_measure_inversion
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T17:02:39.997246+00:00
-- url     : https://prove2.me/submissions/5233d534-d1e0-4910-a49d-47b7432558fd

import Definitions.Def_Formalism_HermitianCurvature_WeylElementCommutesLevelOne
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_BlochKatoDuality
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ConjugationContinuousOnInvertible
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x1_haarUnique
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x1_haarInvFromUnique
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
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P
namespace Formalism.FourierDecayAlt.P
theorem _root_.solution : Formalism.FourierDecayAlt.B2.HaarInv := B2x1.haarInvFromUnique B2x1.haarUnique
end Formalism.FourierDecayAlt.P
