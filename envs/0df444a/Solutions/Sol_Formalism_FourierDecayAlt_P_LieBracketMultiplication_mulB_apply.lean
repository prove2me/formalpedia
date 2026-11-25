-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.LieBracketMultiplication.mulB_apply
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T16:34:28.515495+00:00
-- url     : https://prove2.me/submissions/d28816c8-82de-40dc-a575-81183388a9e1

import Definitions.Def_Formalism_HermitianCurvature_FrameExists2
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LeftDerivativeCurves
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_FrameEntries
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LieBracketMultiplication

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Finset Filter Topology
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.P.QrD
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
open Formalism.FourierDecayAlt.P.LieBracketMultiplication
variable {k r : ℕ}
namespace Formalism.FourierDecayAlt.P.LieBracketMultiplication
theorem _root_.solution (X Y : Mx k r) : mulB k r X Y = X * Y := rfl
end Formalism.FourierDecayAlt.P.LieBracketMultiplication
