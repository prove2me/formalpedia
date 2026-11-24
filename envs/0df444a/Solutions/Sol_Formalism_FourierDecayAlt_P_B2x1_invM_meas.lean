-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.B2x1.invM_meas
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T15:11:29.959817+00:00
-- url     : https://prove2.me/submissions/d53accd6-b134-4602-97cf-6db67adb1351

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
namespace Formalism.FourierDecayAlt.P.B2x1
theorem _root_.solution : Measurable (invM : Mt k r → Mt k r) := by
  rw [invM_smul]; exact detF_cont.measurable.inv.smul adjF_cont.measurable
end Formalism.FourierDecayAlt.P.B2x1
