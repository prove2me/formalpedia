-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.AnisotropicColumnSums.mdim_last
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T01:42:41.127945+00:00
-- url     : https://prove2.me/submissions/3866c284-b2d0-4bf4-8855-59dfbec5dde1

import Definitions.Def_Formalism_HermitianCurvature_FrameMinor
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_OperatorRepresentations
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LemmaDDeterminantIdentity
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_RestrictionIrrelevantDoubleLevelOperator
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_AnisotropicColumnSums

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
open Formalism.FourierDecayAlt.P.AnisotropicColumnSums
variable {k r : ℕ}
namespace Formalism.FourierDecayAlt.P.AnisotropicColumnSums
theorem _root_.solution : mdim k r (Fin.last r) = k + 1 := by
  simp [mdim]
end Formalism.FourierDecayAlt.P.AnisotropicColumnSums
