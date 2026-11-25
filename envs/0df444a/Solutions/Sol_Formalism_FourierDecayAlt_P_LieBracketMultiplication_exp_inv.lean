-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.LieBracketMultiplication.exp_inv
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T07:23:55.607829+00:00
-- url     : https://prove2.me/submissions/41276011-d6d8-4cba-a7ca-477ab34fdccb

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
variable {k r : ℕ} {z : Fin (2 * r + k + 1) → ℂ}
namespace Formalism.FourierDecayAlt.P.LieBracketMultiplication
theorem _root_.solution (X : Mx k r) (s : ℝ) :
    (NormedSpace.exp ((s : ℂ) • X))⁻¹ = NormedSpace.exp (((-s : ℝ) : ℂ) • X) := by
  have e : (((-s : ℝ) : ℂ) • X) = -((s : ℂ) • X) := by
    push_cast
    rw [neg_smul]
  rw [e, Matrix.exp_neg]
end Formalism.FourierDecayAlt.P.LieBracketMultiplication
