-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.CutMP.JA.FFS.mat_inv_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T06:59:36.431602+00:00
-- url     : https://prove2.me/submissions/fdb46baf-09ab-4f62-9262-685752db071c

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CutJAFFStable2
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_RegularisedPairingViaPhase
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_TriangleInequalityAtPlace
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CutJAFFStableEquivOps

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.CutMP Formalism.FourierDecayAlt.P.CutMP.JA Formalism.FourierDecayAlt.P.CutMP.JA.FFS
open Formalism.QuantumDeterminants.WeylGroupFacts
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
noncomputable section
variable {k r : ℕ}
namespace Formalism.FourierDecayAlt.P.CutMP.JA.FFS
theorem _root_.solution : (1 : B.Mat k r)⁻¹ = 1 := by
  simp
end Formalism.FourierDecayAlt.P.CutMP.JA.FFS
