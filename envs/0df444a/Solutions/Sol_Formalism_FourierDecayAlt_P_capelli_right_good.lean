-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.capelli_right_good
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T06:59:06.98744+00:00
-- url     : https://prove2.me/submissions/54cca9b3-20ae-4370-8410-9bef4a6b6957

import Definitions.Def_Formalism_HermitianCurvature_FrameMinor
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_OperatorRepresentations
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_RestrictionIrrelevantDoubleLevelOperator
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CapelliCoordinates
import Theorems.Thm_Formalism_FourierDecayAlt_P_CapelliCoordinates_good_capR

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Finset
open scoped ContDiff
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.Qr
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
namespace Formalism.FourierDecayAlt.P
theorem _root_.solution : Formalism.FourierDecayAlt.Qr.CapRGood := by
  intro E _ _ k r m i D hD Bs hB w
  exact CapelliCoordinates.good_capR hD Bs hB w
end Formalism.FourierDecayAlt.P
